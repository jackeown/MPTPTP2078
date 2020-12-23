%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:55 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  211 (7468 expanded)
%              Number of clauses        :  136 (2558 expanded)
%              Number of leaves         :   18 (1362 expanded)
%              Depth                    :   30
%              Number of atoms          :  603 (40178 expanded)
%              Number of equality atoms :  318 (10732 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f52])).

fof(f90,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3130,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3117,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1023,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_36])).

cnf(c_3116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3122,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4640,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3116,c_3122])).

cnf(c_4747,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1023,c_4640])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3128,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6215,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4747,c_3128])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3460,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3461,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_6321,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6215,c_41,c_3461])).

cnf(c_6322,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6321])).

cnf(c_6332,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3117,c_6322])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6355,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6332,c_3118])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3123,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4474,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_3123])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3125,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5234,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4474,c_3125])).

cnf(c_3466,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3467,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3466])).

cnf(c_3547,plain,
    ( ~ v5_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3754,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3547])).

cnf(c_3755,plain,
    ( v5_relat_1(sK3,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_5312,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5234,c_41,c_3461,c_3467,c_3755])).

cnf(c_6546,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6355,c_5312])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3119,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7867,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_3119])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3530,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4905,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3530])).

cnf(c_8068,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7867,c_38,c_36,c_4905])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1032,c_18])).

cnf(c_3107,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_8074,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8068,c_3107])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3120,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5877,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_3120])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3511,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3848,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3511])).

cnf(c_3849,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3848])).

cnf(c_6249,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5877,c_39,c_41,c_3849])).

cnf(c_8077,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8068,c_6249])).

cnf(c_8100,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8074,c_8077])).

cnf(c_9837,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6332,c_8100])).

cnf(c_9921,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6546,c_9837])).

cnf(c_10216,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9921,c_8077])).

cnf(c_10218,plain,
    ( sK1 = k1_xboole_0
    | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_10216])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8128,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8068,c_3121])).

cnf(c_8253,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8128,c_39,c_41])).

cnf(c_8267,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8253,c_3123])).

cnf(c_19163,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10218,c_5312,c_8267])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_3106,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_3327,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3106])).

cnf(c_8075,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8068,c_3327])).

cnf(c_8092,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8075,c_8077])).

cnf(c_19187,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19163,c_8092])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_19212,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19163,c_34])).

cnf(c_19213,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19212])).

cnf(c_19290,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19187,c_19213])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_19294,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19290,c_3])).

cnf(c_19416,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19213,c_3117])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3134,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4122,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_3124])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3136,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3129,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6918,plain,
    ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3129])).

cnf(c_10776,plain,
    ( k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0) = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4122,c_6918])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3127,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4343,plain,
    ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4122,c_3127])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4344,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4343,c_13])).

cnf(c_10787,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10776,c_4344])).

cnf(c_6214,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_3128])).

cnf(c_3449,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3451,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3449])).

cnf(c_3450,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3453,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3450])).

cnf(c_6893,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6214,c_3451,c_3453])).

cnf(c_6894,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6893])).

cnf(c_10977,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10787,c_6894])).

cnf(c_10980,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10977,c_13])).

cnf(c_19438,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19416,c_10980])).

cnf(c_21153,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19294,c_19438])).

cnf(c_19205,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_19163,c_4640])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_965,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_3110,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3232,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3110,c_4])).

cnf(c_19209,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19163,c_3232])).

cnf(c_19220,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19209,c_19213])).

cnf(c_19221,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19220])).

cnf(c_19211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19163,c_3116])).

cnf(c_19216,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19211,c_19213])).

cnf(c_19218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19216,c_4])).

cnf(c_19224,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19221,c_19218])).

cnf(c_19233,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19205,c_19213,c_19224])).

cnf(c_4124,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_3124])).

cnf(c_4145,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_4124,c_3127])).

cnf(c_19634,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_19233,c_4145])).

cnf(c_21157,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21153,c_19438,c_19634])).

cnf(c_21158,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_21157])).

cnf(c_21160,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21158,c_19218])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.51/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.49  
% 7.51/1.49  ------  iProver source info
% 7.51/1.49  
% 7.51/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.49  git: non_committed_changes: false
% 7.51/1.49  git: last_make_outside_of_git: false
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options
% 7.51/1.49  
% 7.51/1.49  --out_options                           all
% 7.51/1.49  --tptp_safe_out                         true
% 7.51/1.49  --problem_path                          ""
% 7.51/1.49  --include_path                          ""
% 7.51/1.49  --clausifier                            res/vclausify_rel
% 7.51/1.49  --clausifier_options                    --mode clausify
% 7.51/1.49  --stdin                                 false
% 7.51/1.49  --stats_out                             all
% 7.51/1.49  
% 7.51/1.49  ------ General Options
% 7.51/1.49  
% 7.51/1.49  --fof                                   false
% 7.51/1.49  --time_out_real                         305.
% 7.51/1.49  --time_out_virtual                      -1.
% 7.51/1.49  --symbol_type_check                     false
% 7.51/1.49  --clausify_out                          false
% 7.51/1.49  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     num_symb
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       true
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  ------ Parsing...
% 7.51/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  ------ Proving...
% 7.51/1.49  ------ Problem Properties 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  clauses                                 40
% 7.51/1.49  conjectures                             4
% 7.51/1.49  EPR                                     6
% 7.51/1.49  Horn                                    35
% 7.51/1.49  unary                                   10
% 7.51/1.49  binary                                  8
% 7.51/1.49  lits                                    107
% 7.51/1.49  lits eq                                 39
% 7.51/1.49  fd_pure                                 0
% 7.51/1.49  fd_pseudo                               0
% 7.51/1.49  fd_cond                                 3
% 7.51/1.49  fd_pseudo_cond                          1
% 7.51/1.49  AC symbols                              0
% 7.51/1.49  
% 7.51/1.49  ------ Schedule dynamic 5 is on 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  Current options:
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options
% 7.51/1.49  
% 7.51/1.49  --out_options                           all
% 7.51/1.49  --tptp_safe_out                         true
% 7.51/1.49  --problem_path                          ""
% 7.51/1.49  --include_path                          ""
% 7.51/1.49  --clausifier                            res/vclausify_rel
% 7.51/1.49  --clausifier_options                    --mode clausify
% 7.51/1.49  --stdin                                 false
% 7.51/1.49  --stats_out                             all
% 7.51/1.49  
% 7.51/1.49  ------ General Options
% 7.51/1.49  
% 7.51/1.49  --fof                                   false
% 7.51/1.49  --time_out_real                         305.
% 7.51/1.49  --time_out_virtual                      -1.
% 7.51/1.49  --symbol_type_check                     false
% 7.51/1.49  --clausify_out                          false
% 7.51/1.49  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     none
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       false
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS status Theorem for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49   Resolution empty clause
% 7.51/1.49  
% 7.51/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  fof(f8,axiom,(
% 7.51/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f26,plain,(
% 7.51/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f8])).
% 7.51/1.49  
% 7.51/1.49  fof(f50,plain,(
% 7.51/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(nnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f63,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f50])).
% 7.51/1.49  
% 7.51/1.49  fof(f21,conjecture,(
% 7.51/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f22,negated_conjecture,(
% 7.51/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.51/1.49    inference(negated_conjecture,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f45,plain,(
% 7.51/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.51/1.49    inference(ennf_transformation,[],[f22])).
% 7.51/1.49  
% 7.51/1.49  fof(f46,plain,(
% 7.51/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.51/1.49    inference(flattening,[],[f45])).
% 7.51/1.49  
% 7.51/1.49  fof(f52,plain,(
% 7.51/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f53,plain,(
% 7.51/1.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f52])).
% 7.51/1.49  
% 7.51/1.49  fof(f90,plain,(
% 7.51/1.49    r1_tarski(sK2,sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f17,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f37,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(ennf_transformation,[],[f17])).
% 7.51/1.49  
% 7.51/1.49  fof(f38,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(flattening,[],[f37])).
% 7.51/1.49  
% 7.51/1.49  fof(f51,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(nnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f75,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f51])).
% 7.51/1.49  
% 7.51/1.49  fof(f88,plain,(
% 7.51/1.49    v1_funct_2(sK3,sK0,sK1)),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f89,plain,(
% 7.51/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f16,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f36,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(ennf_transformation,[],[f16])).
% 7.51/1.49  
% 7.51/1.49  fof(f74,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f36])).
% 7.51/1.49  
% 7.51/1.49  fof(f11,axiom,(
% 7.51/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f29,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f11])).
% 7.51/1.49  
% 7.51/1.49  fof(f30,plain,(
% 7.51/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(flattening,[],[f29])).
% 7.51/1.49  
% 7.51/1.49  fof(f68,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f30])).
% 7.51/1.49  
% 7.51/1.49  fof(f14,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f34,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(ennf_transformation,[],[f14])).
% 7.51/1.49  
% 7.51/1.49  fof(f72,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f34])).
% 7.51/1.49  
% 7.51/1.49  fof(f20,axiom,(
% 7.51/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f43,plain,(
% 7.51/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.51/1.49    inference(ennf_transformation,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f44,plain,(
% 7.51/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(flattening,[],[f43])).
% 7.51/1.49  
% 7.51/1.49  fof(f86,plain,(
% 7.51/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f44])).
% 7.51/1.49  
% 7.51/1.49  fof(f15,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f23,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.51/1.49    inference(pure_predicate_removal,[],[f15])).
% 7.51/1.49  
% 7.51/1.49  fof(f35,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.51/1.49    inference(ennf_transformation,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f73,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f35])).
% 7.51/1.49  
% 7.51/1.49  fof(f13,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f32,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 7.51/1.49    inference(ennf_transformation,[],[f13])).
% 7.51/1.49  
% 7.51/1.49  fof(f33,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 7.51/1.49    inference(flattening,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f70,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f33])).
% 7.51/1.49  
% 7.51/1.49  fof(f19,axiom,(
% 7.51/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f41,plain,(
% 7.51/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.51/1.49    inference(ennf_transformation,[],[f19])).
% 7.51/1.49  
% 7.51/1.49  fof(f42,plain,(
% 7.51/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.51/1.49    inference(flattening,[],[f41])).
% 7.51/1.49  
% 7.51/1.49  fof(f83,plain,(
% 7.51/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f42])).
% 7.51/1.49  
% 7.51/1.49  fof(f87,plain,(
% 7.51/1.49    v1_funct_1(sK3)),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f85,plain,(
% 7.51/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f44])).
% 7.51/1.49  
% 7.51/1.49  fof(f92,plain,(
% 7.51/1.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f18,axiom,(
% 7.51/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f39,plain,(
% 7.51/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.51/1.49    inference(ennf_transformation,[],[f18])).
% 7.51/1.49  
% 7.51/1.49  fof(f40,plain,(
% 7.51/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.51/1.49    inference(flattening,[],[f39])).
% 7.51/1.49  
% 7.51/1.49  fof(f81,plain,(
% 7.51/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f40])).
% 7.51/1.49  
% 7.51/1.49  fof(f82,plain,(
% 7.51/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f40])).
% 7.51/1.49  
% 7.51/1.49  fof(f91,plain,(
% 7.51/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.51/1.49    inference(cnf_transformation,[],[f53])).
% 7.51/1.49  
% 7.51/1.49  fof(f4,axiom,(
% 7.51/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f47,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.51/1.49    inference(nnf_transformation,[],[f4])).
% 7.51/1.49  
% 7.51/1.49  fof(f48,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.51/1.49    inference(flattening,[],[f47])).
% 7.51/1.49  
% 7.51/1.49  fof(f59,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.51/1.49    inference(cnf_transformation,[],[f48])).
% 7.51/1.49  
% 7.51/1.49  fof(f93,plain,(
% 7.51/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.51/1.49    inference(equality_resolution,[],[f59])).
% 7.51/1.49  
% 7.51/1.49  fof(f5,axiom,(
% 7.51/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f60,plain,(
% 7.51/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f5])).
% 7.51/1.49  
% 7.51/1.49  fof(f2,axiom,(
% 7.51/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f55,plain,(
% 7.51/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f2])).
% 7.51/1.49  
% 7.51/1.49  fof(f9,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f27,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.51/1.49    inference(ennf_transformation,[],[f9])).
% 7.51/1.49  
% 7.51/1.49  fof(f28,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.51/1.49    inference(flattening,[],[f27])).
% 7.51/1.49  
% 7.51/1.49  fof(f65,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f12,axiom,(
% 7.51/1.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f31,plain,(
% 7.51/1.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f12])).
% 7.51/1.49  
% 7.51/1.49  fof(f69,plain,(
% 7.51/1.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f10,axiom,(
% 7.51/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f66,plain,(
% 7.51/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.51/1.49    inference(cnf_transformation,[],[f10])).
% 7.51/1.49  
% 7.51/1.49  fof(f76,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f51])).
% 7.51/1.49  
% 7.51/1.49  fof(f99,plain,(
% 7.51/1.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.51/1.49    inference(equality_resolution,[],[f76])).
% 7.51/1.49  
% 7.51/1.49  fof(f58,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.51/1.49    inference(cnf_transformation,[],[f48])).
% 7.51/1.49  
% 7.51/1.49  fof(f94,plain,(
% 7.51/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.51/1.49    inference(equality_resolution,[],[f58])).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10,plain,
% 7.51/1.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3130,plain,
% 7.51/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.51/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_35,negated_conjecture,
% 7.51/1.49      ( r1_tarski(sK2,sK0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3117,plain,
% 7.51/1.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_26,plain,
% 7.51/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.51/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.51/1.49      | k1_xboole_0 = X2 ),
% 7.51/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_37,negated_conjecture,
% 7.51/1.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1020,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.51/1.49      | sK3 != X0
% 7.51/1.49      | sK1 != X2
% 7.51/1.49      | sK0 != X1
% 7.51/1.49      | k1_xboole_0 = X2 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1021,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.51/1.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.51/1.49      | k1_xboole_0 = sK1 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_1020]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_36,negated_conjecture,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.51/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1023,plain,
% 7.51/1.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.51/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1021,c_36]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3116,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3122,plain,
% 7.51/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.51/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4640,plain,
% 7.51/1.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3116,c_3122]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4747,plain,
% 7.51/1.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_1023,c_4640]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.51/1.49      | ~ v1_relat_1(X1)
% 7.51/1.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3128,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.51/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.51/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6215,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.51/1.49      | sK1 = k1_xboole_0
% 7.51/1.49      | r1_tarski(X0,sK0) != iProver_top
% 7.51/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4747,c_3128]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_41,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_18,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3460,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.51/1.49      | v1_relat_1(sK3) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3461,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.51/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3460]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6321,plain,
% 7.51/1.49      ( r1_tarski(X0,sK0) != iProver_top
% 7.51/1.49      | sK1 = k1_xboole_0
% 7.51/1.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_6215,c_41,c_3461]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6322,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.51/1.49      | sK1 = k1_xboole_0
% 7.51/1.49      | r1_tarski(X0,sK0) != iProver_top ),
% 7.51/1.49      inference(renaming,[status(thm)],[c_6321]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6332,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3117,c_6322]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_30,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.51/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.51/1.49      | ~ v1_funct_1(X0)
% 7.51/1.49      | ~ v1_relat_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3118,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.51/1.49      | v1_funct_1(X0) != iProver_top
% 7.51/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6355,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.51/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.51/1.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6332,c_3118]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19,plain,
% 7.51/1.49      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.51/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3123,plain,
% 7.51/1.49      ( v5_relat_1(X0,X1) = iProver_top
% 7.51/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4474,plain,
% 7.51/1.49      ( v5_relat_1(sK3,sK1) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3116,c_3123]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17,plain,
% 7.51/1.49      ( ~ v5_relat_1(X0,X1)
% 7.51/1.49      | ~ v1_relat_1(X0)
% 7.51/1.49      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3125,plain,
% 7.51/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 7.51/1.49      | v1_relat_1(X0) != iProver_top
% 7.51/1.49      | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5234,plain,
% 7.51/1.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.51/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4474,c_3125]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3466,plain,
% 7.51/1.49      ( v5_relat_1(sK3,sK1)
% 7.51/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3467,plain,
% 7.51/1.49      ( v5_relat_1(sK3,sK1) = iProver_top
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3466]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3547,plain,
% 7.51/1.49      ( ~ v5_relat_1(sK3,X0)
% 7.51/1.49      | v1_relat_1(k7_relat_1(sK3,X1))
% 7.51/1.49      | ~ v1_relat_1(sK3) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3754,plain,
% 7.51/1.49      ( ~ v5_relat_1(sK3,sK1)
% 7.51/1.49      | v1_relat_1(k7_relat_1(sK3,X0))
% 7.51/1.49      | ~ v1_relat_1(sK3) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_3547]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3755,plain,
% 7.51/1.49      ( v5_relat_1(sK3,sK1) != iProver_top
% 7.51/1.49      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.51/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3754]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5312,plain,
% 7.51/1.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_5234,c_41,c_3461,c_3467,c_3755]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6546,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.51/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_6355,c_5312]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_29,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | ~ v1_funct_1(X0)
% 7.51/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.51/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3119,plain,
% 7.51/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.51/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.51/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_7867,plain,
% 7.51/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.51/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3116,c_3119]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_38,negated_conjecture,
% 7.51/1.49      ( v1_funct_1(sK3) ),
% 7.51/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3530,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.51/1.49      | ~ v1_funct_1(sK3)
% 7.51/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4905,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.51/1.49      | ~ v1_funct_1(sK3)
% 7.51/1.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_3530]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8068,plain,
% 7.51/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_7867,c_38,c_36,c_4905]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_31,plain,
% 7.51/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.51/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.51/1.49      | ~ v1_funct_1(X0)
% 7.51/1.49      | ~ v1_relat_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_33,negated_conjecture,
% 7.51/1.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.51/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.51/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1031,plain,
% 7.51/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.51/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.51/1.49      | ~ v1_funct_1(X0)
% 7.51/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.51/1.49      | ~ v1_relat_1(X0)
% 7.51/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.51/1.49      | k1_relat_1(X0) != sK2
% 7.51/1.49      | sK1 != X1 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1032,plain,
% 7.51/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.51/1.49      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.51/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.51/1.49      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.51/1.49      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_1031]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1044,plain,
% 7.51/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.51/1.49      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.51/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.51/1.49      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_1032,c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3107,plain,
% 7.51/1.49      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.51/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 7.51/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8074,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.51/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_8068,c_3107]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_28,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | ~ v1_funct_1(X0)
% 7.51/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3120,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.51/1.49      | v1_funct_1(X0) != iProver_top
% 7.51/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5877,plain,
% 7.51/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.51/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3116,c_3120]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_39,plain,
% 7.51/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3511,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.51/1.49      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 7.51/1.49      | ~ v1_funct_1(sK3) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3848,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.51/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 7.51/1.49      | ~ v1_funct_1(sK3) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_3511]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3849,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.51/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.51/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3848]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6249,plain,
% 7.51/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_5877,c_39,c_41,c_3849]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8077,plain,
% 7.51/1.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_8068,c_6249]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8100,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_8074,c_8077]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9837,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6332,c_8100]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9921,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.51/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6546,c_9837]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10216,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_9921,c_8077]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10218,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0
% 7.51/1.49      | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
% 7.51/1.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3130,c_10216]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_27,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.51/1.49      | ~ v1_funct_1(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3121,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.51/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.51/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8128,plain,
% 7.51/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.51/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_8068,c_3121]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8253,plain,
% 7.51/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_8128,c_39,c_41]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8267,plain,
% 7.51/1.49      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_8253,c_3123]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19163,plain,
% 7.51/1.49      ( sK1 = k1_xboole_0 ),
% 7.51/1.49      inference(forward_subsumption_resolution,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_10218,c_5312,c_8267]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1050,plain,
% 7.51/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.51/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.51/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | sK1 != sK1 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3106,plain,
% 7.51/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | sK1 != sK1
% 7.51/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3327,plain,
% 7.51/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(equality_resolution_simp,[status(thm)],[c_3106]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8075,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.51/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_8068,c_3327]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8092,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_8075,c_8077]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19187,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | sK2 != sK0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19163,c_8092]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_34,negated_conjecture,
% 7.51/1.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19212,plain,
% 7.51/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19163,c_34]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19213,plain,
% 7.51/1.49      ( sK0 = k1_xboole_0 ),
% 7.51/1.49      inference(equality_resolution_simp,[status(thm)],[c_19212]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19290,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | sK2 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_19187,c_19213]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3,plain,
% 7.51/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19294,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | sK2 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19290,c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19416,plain,
% 7.51/1.49      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19213,c_3117]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6,plain,
% 7.51/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3134,plain,
% 7.51/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3124,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.51/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4122,plain,
% 7.51/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3134,c_3124]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1,plain,
% 7.51/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3136,plain,
% 7.51/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1)
% 7.51/1.49      | ~ v1_relat_1(X2)
% 7.51/1.49      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3129,plain,
% 7.51/1.49      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
% 7.51/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.51/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6918,plain,
% 7.51/1.49      ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
% 7.51/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3136,c_3129]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10776,plain,
% 7.51/1.49      ( k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0) = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4122,c_6918]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15,plain,
% 7.51/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3127,plain,
% 7.51/1.49      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4343,plain,
% 7.51/1.49      ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4122,c_3127]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13,plain,
% 7.51/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4344,plain,
% 7.51/1.49      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_4343,c_13]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10787,plain,
% 7.51/1.49      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_10776,c_4344]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6214,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 7.51/1.49      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.51/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_13,c_3128]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3449,plain,
% 7.51/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.51/1.49      | v1_relat_1(k1_xboole_0) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3451,plain,
% 7.51/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.51/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3449]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3450,plain,
% 7.51/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3453,plain,
% 7.51/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3450]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6893,plain,
% 7.51/1.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.51/1.49      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_6214,c_3451,c_3453]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6894,plain,
% 7.51/1.49      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 7.51/1.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.51/1.49      inference(renaming,[status(thm)],[c_6893]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10977,plain,
% 7.51/1.49      ( k1_relat_1(k1_xboole_0) = X0
% 7.51/1.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_10787,c_6894]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10980,plain,
% 7.51/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_10977,c_13]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19438,plain,
% 7.51/1.49      ( sK2 = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_19416,c_10980]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21153,plain,
% 7.51/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.51/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_19294,c_19438]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19205,plain,
% 7.51/1.49      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19163,c_4640]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_25,plain,
% 7.51/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.51/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.51/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_964,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.51/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.51/1.49      | sK3 != X0
% 7.51/1.49      | sK1 != X1
% 7.51/1.49      | sK0 != k1_xboole_0 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_965,plain,
% 7.51/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.51/1.49      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.51/1.49      | sK0 != k1_xboole_0 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_964]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3110,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.51/1.49      | sK0 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4,plain,
% 7.51/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3232,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.51/1.49      | sK0 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_3110,c_4]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19209,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.51/1.49      | sK0 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19163,c_3232]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19220,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.51/1.49      | k1_xboole_0 != k1_xboole_0
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_19209,c_19213]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19221,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.51/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(equality_resolution_simp,[status(thm)],[c_19220]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19211,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19163,c_3116]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19216,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_19211,c_19213]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19218,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19216,c_4]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19224,plain,
% 7.51/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_19221,c_19218]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19233,plain,
% 7.51/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_19205,c_19213,c_19224]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4124,plain,
% 7.51/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3116,c_3124]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4145,plain,
% 7.51/1.49      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4124,c_3127]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19634,plain,
% 7.51/1.49      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_19233,c_4145]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21157,plain,
% 7.51/1.49      ( sK3 != sK3 | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_21153,c_19438,c_19634]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21158,plain,
% 7.51/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.51/1.49      inference(equality_resolution_simp,[status(thm)],[c_21157]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21160,plain,
% 7.51/1.49      ( $false ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_21158,c_19218]) ).
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  ------                               Statistics
% 7.51/1.49  
% 7.51/1.49  ------ General
% 7.51/1.49  
% 7.51/1.49  abstr_ref_over_cycles:                  0
% 7.51/1.49  abstr_ref_under_cycles:                 0
% 7.51/1.49  gc_basic_clause_elim:                   0
% 7.51/1.49  forced_gc_time:                         0
% 7.51/1.49  parsing_time:                           0.007
% 7.51/1.49  unif_index_cands_time:                  0.
% 7.51/1.49  unif_index_add_time:                    0.
% 7.51/1.49  orderings_time:                         0.
% 7.51/1.49  out_proof_time:                         0.021
% 7.51/1.49  total_time:                             0.585
% 7.51/1.49  num_of_symbols:                         50
% 7.51/1.49  num_of_terms:                           17116
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing
% 7.51/1.49  
% 7.51/1.49  num_of_splits:                          0
% 7.51/1.49  num_of_split_atoms:                     0
% 7.51/1.49  num_of_reused_defs:                     0
% 7.51/1.49  num_eq_ax_congr_red:                    4
% 7.51/1.49  num_of_sem_filtered_clauses:            1
% 7.51/1.49  num_of_subtypes:                        0
% 7.51/1.49  monotx_restored_types:                  0
% 7.51/1.49  sat_num_of_epr_types:                   0
% 7.51/1.49  sat_num_of_non_cyclic_types:            0
% 7.51/1.49  sat_guarded_non_collapsed_types:        0
% 7.51/1.49  num_pure_diseq_elim:                    0
% 7.51/1.49  simp_replaced_by:                       0
% 7.51/1.49  res_preprocessed:                       149
% 7.51/1.49  prep_upred:                             0
% 7.51/1.49  prep_unflattend:                        156
% 7.51/1.49  smt_new_axioms:                         0
% 7.51/1.49  pred_elim_cands:                        7
% 7.51/1.49  pred_elim:                              1
% 7.51/1.49  pred_elim_cl:                           -2
% 7.51/1.49  pred_elim_cycles:                       4
% 7.51/1.49  merged_defs:                            6
% 7.51/1.49  merged_defs_ncl:                        0
% 7.51/1.49  bin_hyper_res:                          6
% 7.51/1.49  prep_cycles:                            3
% 7.51/1.49  pred_elim_time:                         0.024
% 7.51/1.49  splitting_time:                         0.
% 7.51/1.49  sem_filter_time:                        0.
% 7.51/1.49  monotx_time:                            0.
% 7.51/1.49  subtype_inf_time:                       0.
% 7.51/1.49  
% 7.51/1.49  ------ Problem properties
% 7.51/1.49  
% 7.51/1.49  clauses:                                40
% 7.51/1.49  conjectures:                            4
% 7.51/1.49  epr:                                    6
% 7.51/1.49  horn:                                   35
% 7.51/1.49  ground:                                 15
% 7.51/1.49  unary:                                  10
% 7.51/1.49  binary:                                 8
% 7.51/1.49  lits:                                   107
% 7.51/1.49  lits_eq:                                39
% 7.51/1.49  fd_pure:                                0
% 7.51/1.49  fd_pseudo:                              0
% 7.51/1.49  fd_cond:                                3
% 7.51/1.49  fd_pseudo_cond:                         1
% 7.51/1.49  ac_symbols:                             0
% 7.51/1.49  
% 7.51/1.49  ------ Propositional Solver
% 7.51/1.49  
% 7.51/1.49  prop_solver_calls:                      28
% 7.51/1.49  prop_fast_solver_calls:                 1987
% 7.51/1.49  smt_solver_calls:                       0
% 7.51/1.49  smt_fast_solver_calls:                  0
% 7.51/1.49  prop_num_of_clauses:                    7757
% 7.51/1.49  prop_preprocess_simplified:             15303
% 7.51/1.49  prop_fo_subsumed:                       41
% 7.51/1.49  prop_solver_time:                       0.
% 7.51/1.49  smt_solver_time:                        0.
% 7.51/1.49  smt_fast_solver_time:                   0.
% 7.51/1.49  prop_fast_solver_time:                  0.
% 7.51/1.49  prop_unsat_core_time:                   0.
% 7.51/1.49  
% 7.51/1.49  ------ QBF
% 7.51/1.49  
% 7.51/1.49  qbf_q_res:                              0
% 7.51/1.49  qbf_num_tautologies:                    0
% 7.51/1.49  qbf_prep_cycles:                        0
% 7.51/1.49  
% 7.51/1.49  ------ BMC1
% 7.51/1.49  
% 7.51/1.49  bmc1_current_bound:                     -1
% 7.51/1.49  bmc1_last_solved_bound:                 -1
% 7.51/1.49  bmc1_unsat_core_size:                   -1
% 7.51/1.49  bmc1_unsat_core_parents_size:           -1
% 7.51/1.49  bmc1_merge_next_fun:                    0
% 7.51/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation
% 7.51/1.49  
% 7.51/1.49  inst_num_of_clauses:                    2294
% 7.51/1.49  inst_num_in_passive:                    797
% 7.51/1.49  inst_num_in_active:                     1061
% 7.51/1.49  inst_num_in_unprocessed:                436
% 7.51/1.49  inst_num_of_loops:                      1200
% 7.51/1.49  inst_num_of_learning_restarts:          0
% 7.51/1.49  inst_num_moves_active_passive:          135
% 7.51/1.49  inst_lit_activity:                      0
% 7.51/1.49  inst_lit_activity_moves:                0
% 7.51/1.49  inst_num_tautologies:                   0
% 7.51/1.49  inst_num_prop_implied:                  0
% 7.51/1.49  inst_num_existing_simplified:           0
% 7.51/1.49  inst_num_eq_res_simplified:             0
% 7.51/1.49  inst_num_child_elim:                    0
% 7.51/1.49  inst_num_of_dismatching_blockings:      1101
% 7.51/1.49  inst_num_of_non_proper_insts:           2636
% 7.51/1.49  inst_num_of_duplicates:                 0
% 7.51/1.49  inst_inst_num_from_inst_to_res:         0
% 7.51/1.49  inst_dismatching_checking_time:         0.
% 7.51/1.49  
% 7.51/1.49  ------ Resolution
% 7.51/1.49  
% 7.51/1.49  res_num_of_clauses:                     0
% 7.51/1.49  res_num_in_passive:                     0
% 7.51/1.49  res_num_in_active:                      0
% 7.51/1.49  res_num_of_loops:                       152
% 7.51/1.49  res_forward_subset_subsumed:            61
% 7.51/1.49  res_backward_subset_subsumed:           2
% 7.51/1.49  res_forward_subsumed:                   2
% 7.51/1.49  res_backward_subsumed:                  1
% 7.51/1.49  res_forward_subsumption_resolution:     6
% 7.51/1.49  res_backward_subsumption_resolution:    0
% 7.51/1.49  res_clause_to_clause_subsumption:       1343
% 7.51/1.49  res_orphan_elimination:                 0
% 7.51/1.49  res_tautology_del:                      200
% 7.51/1.49  res_num_eq_res_simplified:              1
% 7.51/1.49  res_num_sel_changes:                    0
% 7.51/1.49  res_moves_from_active_to_pass:          0
% 7.51/1.49  
% 7.51/1.49  ------ Superposition
% 7.51/1.49  
% 7.51/1.49  sup_time_total:                         0.
% 7.51/1.49  sup_time_generating:                    0.
% 7.51/1.49  sup_time_sim_full:                      0.
% 7.51/1.49  sup_time_sim_immed:                     0.
% 7.51/1.49  
% 7.51/1.49  sup_num_of_clauses:                     254
% 7.51/1.49  sup_num_in_active:                      82
% 7.51/1.49  sup_num_in_passive:                     172
% 7.51/1.49  sup_num_of_loops:                       238
% 7.51/1.49  sup_fw_superposition:                   437
% 7.51/1.49  sup_bw_superposition:                   320
% 7.51/1.49  sup_immediate_simplified:               239
% 7.51/1.49  sup_given_eliminated:                   3
% 7.51/1.49  comparisons_done:                       0
% 7.51/1.49  comparisons_avoided:                    112
% 7.51/1.49  
% 7.51/1.49  ------ Simplifications
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  sim_fw_subset_subsumed:                 54
% 7.51/1.49  sim_bw_subset_subsumed:                 104
% 7.51/1.49  sim_fw_subsumed:                        58
% 7.51/1.49  sim_bw_subsumed:                        2
% 7.51/1.49  sim_fw_subsumption_res:                 30
% 7.51/1.49  sim_bw_subsumption_res:                 0
% 7.51/1.49  sim_tautology_del:                      38
% 7.51/1.49  sim_eq_tautology_del:                   63
% 7.51/1.49  sim_eq_res_simp:                        6
% 7.51/1.49  sim_fw_demodulated:                     63
% 7.51/1.49  sim_bw_demodulated:                     120
% 7.51/1.49  sim_light_normalised:                   103
% 7.51/1.49  sim_joinable_taut:                      0
% 7.51/1.49  sim_joinable_simp:                      0
% 7.51/1.49  sim_ac_normalised:                      0
% 7.51/1.49  sim_smt_subsumption:                    0
% 7.51/1.49  
%------------------------------------------------------------------------------
