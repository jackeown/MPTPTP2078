%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:50 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  182 (4172 expanded)
%              Number of clauses        :  114 (1354 expanded)
%              Number of leaves         :   18 ( 783 expanded)
%              Depth                    :   24
%              Number of atoms          :  566 (23244 expanded)
%              Number of equality atoms :  279 (6181 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f51])).

fof(f88,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f95])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1433,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_574,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_576,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_35])).

cnf(c_1432,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1438,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3215,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1432,c_1438])).

cnf(c_3398,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_576,c_3215])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1442,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4035,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_1442])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1726,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1727,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_4187,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4035,c_40,c_1727])).

cnf(c_4188,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4187])).

cnf(c_4199,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1433,c_4188])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1434,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4230,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4199,c_1434])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1435,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4788,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_1435])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1806,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1904,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_4958,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_37,c_35,c_1904])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_584,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_585,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_376,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_16])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_585,c_16,c_377])).

cnf(c_1421,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_4965,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4958,c_1421])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1436,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4426,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_1436])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1893,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_1894,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_4950,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4426,c_38,c_40,c_1894])).

cnf(c_4967,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4958,c_4950])).

cnf(c_4981,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4965,c_4967])).

cnf(c_5487,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4199,c_4981])).

cnf(c_5578,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_5487])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5730,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_1437])).

cnf(c_6167,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5730,c_38,c_40])).

cnf(c_1440,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6181,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6167,c_1440])).

cnf(c_1430,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_6180,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6167,c_1430])).

cnf(c_7009,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5578,c_6181,c_4967,c_6180])).

cnf(c_7015,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7009,c_6167])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7030,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7009,c_33])).

cnf(c_7031,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7030])).

cnf(c_7078,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7015,c_7031])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7080,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7078,c_7])).

cnf(c_20,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_401,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_402,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_402,c_9])).

cnf(c_1429,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_422,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1989,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_1990,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1989])).

cnf(c_2008,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1429,c_38,c_40,c_422,c_1990])).

cnf(c_2009,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2008])).

cnf(c_4963,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4958,c_2009])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1749,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_883,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1928,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_884,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2288,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_2289,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2288])).

cnf(c_886,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1914,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_2359,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_3466,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3709,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5229,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4963,c_34,c_33,c_108,c_109,c_1749,c_1928,c_2289,c_3466,c_3709,c_4199,c_4981])).

cnf(c_7019,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7009,c_5229])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7059,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7019,c_6])).

cnf(c_7082,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7080,c_7059])).

cnf(c_7017,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7009,c_4981])).

cnf(c_7070,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7017,c_6])).

cnf(c_7083,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7080,c_7070])).

cnf(c_7093,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7082,c_7083])).

cnf(c_2157,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1817,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1819,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7093,c_2157,c_1819,c_1726,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.38/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/1.00  
% 3.38/1.00  ------  iProver source info
% 3.38/1.00  
% 3.38/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.38/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/1.00  git: non_committed_changes: false
% 3.38/1.00  git: last_make_outside_of_git: false
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    --mode clausify
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         false
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     num_symb
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       true
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     false
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   []
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_full_bw                           [BwDemod]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  ------ Parsing...
% 3.38/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/1.00  ------ Proving...
% 3.38/1.00  ------ Problem Properties 
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  clauses                                 36
% 3.38/1.00  conjectures                             4
% 3.38/1.00  EPR                                     8
% 3.38/1.00  Horn                                    31
% 3.38/1.00  unary                                   10
% 3.38/1.00  binary                                  8
% 3.38/1.00  lits                                    93
% 3.38/1.00  lits eq                                 36
% 3.38/1.00  fd_pure                                 0
% 3.38/1.00  fd_pseudo                               0
% 3.38/1.00  fd_cond                                 4
% 3.38/1.00  fd_pseudo_cond                          1
% 3.38/1.00  AC symbols                              0
% 3.38/1.00  
% 3.38/1.00  ------ Schedule dynamic 5 is on 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  Current options:
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    --mode clausify
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         false
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     none
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       false
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     false
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   []
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_full_bw                           [BwDemod]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ Proving...
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  % SZS status Theorem for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  fof(f21,conjecture,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f22,negated_conjecture,(
% 3.38/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.38/1.00    inference(negated_conjecture,[],[f21])).
% 3.38/1.00  
% 3.38/1.00  fof(f43,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.38/1.00    inference(ennf_transformation,[],[f22])).
% 3.38/1.00  
% 3.38/1.00  fof(f44,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.38/1.00    inference(flattening,[],[f43])).
% 3.38/1.00  
% 3.38/1.00  fof(f51,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f52,plain,(
% 3.38/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f51])).
% 3.38/1.00  
% 3.38/1.00  fof(f88,plain,(
% 3.38/1.00    r1_tarski(sK2,sK0)),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f17,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f35,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(ennf_transformation,[],[f17])).
% 3.38/1.00  
% 3.38/1.00  fof(f36,plain,(
% 3.38/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(flattening,[],[f35])).
% 3.38/1.00  
% 3.38/1.00  fof(f50,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(nnf_transformation,[],[f36])).
% 3.38/1.00  
% 3.38/1.00  fof(f73,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f50])).
% 3.38/1.00  
% 3.38/1.00  fof(f86,plain,(
% 3.38/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f87,plain,(
% 3.38/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f16,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f34,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(ennf_transformation,[],[f16])).
% 3.38/1.00  
% 3.38/1.00  fof(f72,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f34])).
% 3.38/1.00  
% 3.38/1.00  fof(f11,axiom,(
% 3.38/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f28,plain,(
% 3.38/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.38/1.00    inference(ennf_transformation,[],[f11])).
% 3.38/1.00  
% 3.38/1.00  fof(f29,plain,(
% 3.38/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.38/1.00    inference(flattening,[],[f28])).
% 3.38/1.00  
% 3.38/1.00  fof(f67,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f29])).
% 3.38/1.00  
% 3.38/1.00  fof(f13,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f31,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(ennf_transformation,[],[f13])).
% 3.38/1.00  
% 3.38/1.00  fof(f69,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f31])).
% 3.38/1.00  
% 3.38/1.00  fof(f20,axiom,(
% 3.38/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f41,plain,(
% 3.38/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.38/1.00    inference(ennf_transformation,[],[f20])).
% 3.38/1.00  
% 3.38/1.00  fof(f42,plain,(
% 3.38/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.38/1.00    inference(flattening,[],[f41])).
% 3.38/1.00  
% 3.38/1.00  fof(f84,plain,(
% 3.38/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f19,axiom,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f39,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.38/1.00    inference(ennf_transformation,[],[f19])).
% 3.38/1.00  
% 3.38/1.00  fof(f40,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.38/1.00    inference(flattening,[],[f39])).
% 3.38/1.00  
% 3.38/1.00  fof(f81,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f40])).
% 3.38/1.00  
% 3.38/1.00  fof(f85,plain,(
% 3.38/1.00    v1_funct_1(sK3)),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f83,plain,(
% 3.38/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f90,plain,(
% 3.38/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f14,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f23,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.38/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.38/1.00  
% 3.38/1.00  fof(f32,plain,(
% 3.38/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/1.00    inference(ennf_transformation,[],[f23])).
% 3.38/1.00  
% 3.38/1.00  fof(f70,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f32])).
% 3.38/1.00  
% 3.38/1.00  fof(f8,axiom,(
% 3.38/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f26,plain,(
% 3.38/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.38/1.00    inference(ennf_transformation,[],[f8])).
% 3.38/1.00  
% 3.38/1.00  fof(f49,plain,(
% 3.38/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.38/1.00    inference(nnf_transformation,[],[f26])).
% 3.38/1.00  
% 3.38/1.00  fof(f63,plain,(
% 3.38/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f49])).
% 3.38/1.00  
% 3.38/1.00  fof(f18,axiom,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f37,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.38/1.00    inference(ennf_transformation,[],[f18])).
% 3.38/1.00  
% 3.38/1.00  fof(f38,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.38/1.00    inference(flattening,[],[f37])).
% 3.38/1.00  
% 3.38/1.00  fof(f79,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f38])).
% 3.38/1.00  
% 3.38/1.00  fof(f80,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f38])).
% 3.38/1.00  
% 3.38/1.00  fof(f89,plain,(
% 3.38/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.38/1.00    inference(cnf_transformation,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f5,axiom,(
% 3.38/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f47,plain,(
% 3.38/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.38/1.00    inference(nnf_transformation,[],[f5])).
% 3.38/1.00  
% 3.38/1.00  fof(f48,plain,(
% 3.38/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.38/1.00    inference(flattening,[],[f47])).
% 3.38/1.00  
% 3.38/1.00  fof(f60,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.38/1.00    inference(cnf_transformation,[],[f48])).
% 3.38/1.00  
% 3.38/1.00  fof(f94,plain,(
% 3.38/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.38/1.00    inference(equality_resolution,[],[f60])).
% 3.38/1.00  
% 3.38/1.00  fof(f78,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f50])).
% 3.38/1.00  
% 3.38/1.00  fof(f95,plain,(
% 3.38/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/1.00    inference(equality_resolution,[],[f78])).
% 3.38/1.00  
% 3.38/1.00  fof(f96,plain,(
% 3.38/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.38/1.00    inference(equality_resolution,[],[f95])).
% 3.38/1.00  
% 3.38/1.00  fof(f6,axiom,(
% 3.38/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f62,plain,(
% 3.38/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f6])).
% 3.38/1.00  
% 3.38/1.00  fof(f59,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f48])).
% 3.38/1.00  
% 3.38/1.00  fof(f3,axiom,(
% 3.38/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f45,plain,(
% 3.38/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.38/1.00    inference(nnf_transformation,[],[f3])).
% 3.38/1.00  
% 3.38/1.00  fof(f46,plain,(
% 3.38/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.38/1.00    inference(flattening,[],[f45])).
% 3.38/1.00  
% 3.38/1.00  fof(f57,plain,(
% 3.38/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f46])).
% 3.38/1.00  
% 3.38/1.00  fof(f4,axiom,(
% 3.38/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f58,plain,(
% 3.38/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f4])).
% 3.38/1.00  
% 3.38/1.00  fof(f61,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.38/1.00    inference(cnf_transformation,[],[f48])).
% 3.38/1.00  
% 3.38/1.00  fof(f93,plain,(
% 3.38/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.38/1.00    inference(equality_resolution,[],[f61])).
% 3.38/1.00  
% 3.38/1.00  cnf(c_34,negated_conjecture,
% 3.38/1.00      ( r1_tarski(sK2,sK0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1433,plain,
% 3.38/1.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_25,plain,
% 3.38/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.38/1.00      | k1_xboole_0 = X2 ),
% 3.38/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_36,negated_conjecture,
% 3.38/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.38/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_573,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.38/1.00      | sK3 != X0
% 3.38/1.00      | sK1 != X2
% 3.38/1.00      | sK0 != X1
% 3.38/1.00      | k1_xboole_0 = X2 ),
% 3.38/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_574,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.38/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.38/1.00      | k1_xboole_0 = sK1 ),
% 3.38/1.00      inference(unflattening,[status(thm)],[c_573]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_35,negated_conjecture,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.38/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_576,plain,
% 3.38/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_574,c_35]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1432,plain,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_19,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1438,plain,
% 3.38/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.38/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3215,plain,
% 3.38/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1432,c_1438]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3398,plain,
% 3.38/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_576,c_3215]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_14,plain,
% 3.38/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.38/1.00      | ~ v1_relat_1(X1)
% 3.38/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.38/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1442,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.38/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.38/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4035,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.38/1.00      | sK1 = k1_xboole_0
% 3.38/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.38/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_3398,c_1442]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_40,plain,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_16,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | v1_relat_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1726,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.38/1.00      | v1_relat_1(sK3) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1727,plain,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.38/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4187,plain,
% 3.38/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.38/1.00      | sK1 = k1_xboole_0
% 3.38/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_4035,c_40,c_1727]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4188,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.38/1.00      | sK1 = k1_xboole_0
% 3.38/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.38/1.00      inference(renaming,[status(thm)],[c_4187]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4199,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1433,c_4188]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_29,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.38/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.38/1.00      | ~ v1_funct_1(X0)
% 3.38/1.00      | ~ v1_relat_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1434,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.38/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.38/1.00      | v1_funct_1(X0) != iProver_top
% 3.38/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4230,plain,
% 3.38/1.00      ( sK1 = k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.38/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.38/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.38/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_4199,c_1434]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_28,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | ~ v1_funct_1(X0)
% 3.38/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.38/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1435,plain,
% 3.38/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.38/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.38/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4788,plain,
% 3.38/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.38/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1432,c_1435]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_37,negated_conjecture,
% 3.38/1.00      ( v1_funct_1(sK3) ),
% 3.38/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1806,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.38/1.00      | ~ v1_funct_1(sK3)
% 3.38/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1904,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.38/1.00      | ~ v1_funct_1(sK3)
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_1806]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4958,plain,
% 3.38/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_4788,c_37,c_35,c_1904]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_30,plain,
% 3.38/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.38/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.38/1.00      | ~ v1_funct_1(X0)
% 3.38/1.00      | ~ v1_relat_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_32,negated_conjecture,
% 3.38/1.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.38/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_584,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.38/1.00      | ~ v1_funct_1(X0)
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | ~ v1_relat_1(X0)
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.38/1.00      | k1_relat_1(X0) != sK2
% 3.38/1.00      | sK1 != X1 ),
% 3.38/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_585,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.38/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_17,plain,
% 3.38/1.00      ( v5_relat_1(X0,X1)
% 3.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.38/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_11,plain,
% 3.38/1.00      ( ~ v5_relat_1(X0,X1)
% 3.38/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.38/1.00      | ~ v1_relat_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_372,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.38/1.00      | ~ v1_relat_1(X0) ),
% 3.38/1.00      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_376,plain,
% 3.38/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_372,c_16]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_377,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.38/1.00      inference(renaming,[status(thm)],[c_376]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_597,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.38/1.00      inference(forward_subsumption_resolution,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_585,c_16,c_377]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1421,plain,
% 3.38/1.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.38/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4965,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_4958,c_1421]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_27,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | ~ v1_funct_1(X0)
% 3.38/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1436,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.38/1.00      | v1_funct_1(X0) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4426,plain,
% 3.38/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.38/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1432,c_1436]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_38,plain,
% 3.38/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1778,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.38/1.00      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.38/1.00      | ~ v1_funct_1(sK3) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1893,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.38/1.00      | ~ v1_funct_1(sK3) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_1778]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1894,plain,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.38/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4950,plain,
% 3.38/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_4426,c_38,c_40,c_1894]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4967,plain,
% 3.38/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_4958,c_4950]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4981,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.38/1.00      inference(forward_subsumption_resolution,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_4965,c_4967]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_5487,plain,
% 3.38/1.00      ( sK1 = k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_4199,c_4981]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_5578,plain,
% 3.38/1.00      ( sK1 = k1_xboole_0
% 3.38/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.38/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.38/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_4230,c_5487]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_26,plain,
% 3.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/1.00      | ~ v1_funct_1(X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1437,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.38/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.38/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_5730,plain,
% 3.38/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.38/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_4958,c_1437]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_6167,plain,
% 3.38/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_5730,c_38,c_40]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1440,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.38/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_6181,plain,
% 3.38/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_6167,c_1440]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1430,plain,
% 3.38/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.38/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_6180,plain,
% 3.38/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_6167,c_1430]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7009,plain,
% 3.38/1.00      ( sK1 = k1_xboole_0 ),
% 3.38/1.00      inference(forward_subsumption_resolution,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_5578,c_6181,c_4967,c_6180]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7015,plain,
% 3.38/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7009,c_6167]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_33,negated_conjecture,
% 3.38/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.38/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7030,plain,
% 3.38/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7009,c_33]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7031,plain,
% 3.38/1.00      ( sK0 = k1_xboole_0 ),
% 3.38/1.00      inference(equality_resolution_simp,[status(thm)],[c_7030]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7078,plain,
% 3.38/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.38/1.00      inference(light_normalisation,[status(thm)],[c_7015,c_7031]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7,plain,
% 3.38/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.38/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7080,plain,
% 3.38/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7078,c_7]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_20,plain,
% 3.38/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.38/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.38/1.00      | k1_xboole_0 = X0 ),
% 3.38/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_401,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK2 != X0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = X0 ),
% 3.38/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_402,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK2 ),
% 3.38/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_9,plain,
% 3.38/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_416,plain,
% 3.38/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.38/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK2 ),
% 3.38/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_402,c_9]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1429,plain,
% 3.38/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK2
% 3.38/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_422,plain,
% 3.38/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK2
% 3.38/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1989,plain,
% 3.38/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.38/1.00      | ~ v1_funct_1(sK3) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_1893]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1990,plain,
% 3.38/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.38/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.38/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_1989]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2008,plain,
% 3.38/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.38/1.00      | k1_xboole_0 = sK2
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_1429,c_38,c_40,c_422,c_1990]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2009,plain,
% 3.38/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK2
% 3.38/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.38/1.00      inference(renaming,[status(thm)],[c_2008]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_4963,plain,
% 3.38/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.38/1.00      | sK2 = k1_xboole_0
% 3.38/1.00      | sK1 != k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_4958,c_2009]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_8,plain,
% 3.38/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = X0
% 3.38/1.00      | k1_xboole_0 = X1 ),
% 3.38/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_108,plain,
% 3.38/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_109,plain,
% 3.38/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2,plain,
% 3.38/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.38/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1749,plain,
% 3.38/1.00      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.38/1.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.38/1.00      | sK2 = k1_xboole_0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_883,plain,( X0 = X0 ),theory(equality) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1928,plain,
% 3.38/1.00      ( sK2 = sK2 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_883]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_884,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2288,plain,
% 3.38/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_884]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2289,plain,
% 3.38/1.00      ( sK1 != k1_xboole_0
% 3.38/1.00      | k1_xboole_0 = sK1
% 3.38/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_2288]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_886,plain,
% 3.38/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.38/1.00      theory(equality) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1914,plain,
% 3.38/1.00      ( ~ r1_tarski(X0,X1)
% 3.38/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.38/1.00      | sK2 != X0
% 3.38/1.00      | k1_xboole_0 != X1 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_886]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2359,plain,
% 3.38/1.00      ( ~ r1_tarski(sK2,X0)
% 3.38/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.38/1.00      | sK2 != sK2
% 3.38/1.00      | k1_xboole_0 != X0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_1914]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3466,plain,
% 3.38/1.00      ( ~ r1_tarski(sK2,sK0)
% 3.38/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.38/1.00      | sK2 != sK2
% 3.38/1.00      | k1_xboole_0 != sK0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_2359]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_5,plain,
% 3.38/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3709,plain,
% 3.38/1.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_5229,plain,
% 3.38/1.00      ( sK2 = k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.38/1.00      inference(global_propositional_subsumption,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_4963,c_34,c_33,c_108,c_109,c_1749,c_1928,c_2289,
% 3.38/1.00                 c_3466,c_3709,c_4199,c_4981]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7019,plain,
% 3.38/1.00      ( sK2 = k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7009,c_5229]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_6,plain,
% 3.38/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.38/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7059,plain,
% 3.38/1.00      ( sK2 = k1_xboole_0
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7019,c_6]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7082,plain,
% 3.38/1.00      ( sK2 = k1_xboole_0 ),
% 3.38/1.00      inference(backward_subsumption_resolution,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_7080,c_7059]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7017,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7009,c_4981]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7070,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.38/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7017,c_6]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7083,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
% 3.38/1.00      inference(backward_subsumption_resolution,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_7080,c_7070]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_7093,plain,
% 3.38/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_7082,c_7083]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2157,plain,
% 3.38/1.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1817,plain,
% 3.38/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.38/1.00      | ~ v1_relat_1(sK3)
% 3.38/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1819,plain,
% 3.38/1.00      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.38/1.00      | ~ v1_relat_1(sK3)
% 3.38/1.00      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_1817]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(contradiction,plain,
% 3.38/1.00      ( $false ),
% 3.38/1.00      inference(minisat,[status(thm)],[c_7093,c_2157,c_1819,c_1726,c_35]) ).
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  ------                               Statistics
% 3.38/1.00  
% 3.38/1.00  ------ General
% 3.38/1.00  
% 3.38/1.00  abstr_ref_over_cycles:                  0
% 3.38/1.00  abstr_ref_under_cycles:                 0
% 3.38/1.00  gc_basic_clause_elim:                   0
% 3.38/1.00  forced_gc_time:                         0
% 3.38/1.00  parsing_time:                           0.02
% 3.38/1.00  unif_index_cands_time:                  0.
% 3.38/1.00  unif_index_add_time:                    0.
% 3.38/1.00  orderings_time:                         0.
% 3.38/1.00  out_proof_time:                         0.019
% 3.38/1.00  total_time:                             0.32
% 3.38/1.00  num_of_symbols:                         50
% 3.38/1.00  num_of_terms:                           6031
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing
% 3.38/1.00  
% 3.38/1.00  num_of_splits:                          0
% 3.38/1.00  num_of_split_atoms:                     0
% 3.38/1.00  num_of_reused_defs:                     0
% 3.38/1.00  num_eq_ax_congr_red:                    10
% 3.38/1.00  num_of_sem_filtered_clauses:            1
% 3.38/1.00  num_of_subtypes:                        0
% 3.38/1.00  monotx_restored_types:                  0
% 3.38/1.00  sat_num_of_epr_types:                   0
% 3.38/1.00  sat_num_of_non_cyclic_types:            0
% 3.38/1.00  sat_guarded_non_collapsed_types:        0
% 3.38/1.00  num_pure_diseq_elim:                    0
% 3.38/1.00  simp_replaced_by:                       0
% 3.38/1.00  res_preprocessed:                       171
% 3.38/1.00  prep_upred:                             0
% 3.38/1.00  prep_unflattend:                        43
% 3.38/1.00  smt_new_axioms:                         0
% 3.38/1.00  pred_elim_cands:                        5
% 3.38/1.00  pred_elim:                              2
% 3.38/1.00  pred_elim_cl:                           0
% 3.38/1.00  pred_elim_cycles:                       4
% 3.38/1.00  merged_defs:                            0
% 3.38/1.00  merged_defs_ncl:                        0
% 3.38/1.00  bin_hyper_res:                          0
% 3.38/1.00  prep_cycles:                            4
% 3.38/1.00  pred_elim_time:                         0.009
% 3.38/1.00  splitting_time:                         0.
% 3.38/1.00  sem_filter_time:                        0.
% 3.38/1.00  monotx_time:                            0.001
% 3.38/1.00  subtype_inf_time:                       0.
% 3.38/1.00  
% 3.38/1.00  ------ Problem properties
% 3.38/1.00  
% 3.38/1.00  clauses:                                36
% 3.38/1.00  conjectures:                            4
% 3.38/1.00  epr:                                    8
% 3.38/1.00  horn:                                   31
% 3.38/1.00  ground:                                 13
% 3.38/1.00  unary:                                  10
% 3.38/1.00  binary:                                 8
% 3.38/1.00  lits:                                   93
% 3.38/1.00  lits_eq:                                36
% 3.38/1.00  fd_pure:                                0
% 3.38/1.00  fd_pseudo:                              0
% 3.38/1.00  fd_cond:                                4
% 3.38/1.00  fd_pseudo_cond:                         1
% 3.38/1.00  ac_symbols:                             0
% 3.38/1.00  
% 3.38/1.00  ------ Propositional Solver
% 3.38/1.00  
% 3.38/1.00  prop_solver_calls:                      26
% 3.38/1.00  prop_fast_solver_calls:                 1223
% 3.38/1.00  smt_solver_calls:                       0
% 3.38/1.00  smt_fast_solver_calls:                  0
% 3.38/1.00  prop_num_of_clauses:                    2640
% 3.38/1.00  prop_preprocess_simplified:             7730
% 3.38/1.00  prop_fo_subsumed:                       22
% 3.38/1.00  prop_solver_time:                       0.
% 3.38/1.00  smt_solver_time:                        0.
% 3.38/1.00  smt_fast_solver_time:                   0.
% 3.38/1.00  prop_fast_solver_time:                  0.
% 3.38/1.00  prop_unsat_core_time:                   0.
% 3.38/1.00  
% 3.38/1.00  ------ QBF
% 3.38/1.00  
% 3.38/1.00  qbf_q_res:                              0
% 3.38/1.00  qbf_num_tautologies:                    0
% 3.38/1.00  qbf_prep_cycles:                        0
% 3.38/1.00  
% 3.38/1.00  ------ BMC1
% 3.38/1.00  
% 3.38/1.00  bmc1_current_bound:                     -1
% 3.38/1.00  bmc1_last_solved_bound:                 -1
% 3.38/1.00  bmc1_unsat_core_size:                   -1
% 3.38/1.00  bmc1_unsat_core_parents_size:           -1
% 3.38/1.00  bmc1_merge_next_fun:                    0
% 3.38/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation
% 3.38/1.00  
% 3.38/1.00  inst_num_of_clauses:                    825
% 3.38/1.00  inst_num_in_passive:                    50
% 3.38/1.00  inst_num_in_active:                     371
% 3.38/1.00  inst_num_in_unprocessed:                405
% 3.38/1.00  inst_num_of_loops:                      450
% 3.38/1.00  inst_num_of_learning_restarts:          0
% 3.38/1.00  inst_num_moves_active_passive:          78
% 3.38/1.00  inst_lit_activity:                      0
% 3.38/1.00  inst_lit_activity_moves:                0
% 3.38/1.00  inst_num_tautologies:                   0
% 3.38/1.00  inst_num_prop_implied:                  0
% 3.38/1.00  inst_num_existing_simplified:           0
% 3.38/1.00  inst_num_eq_res_simplified:             0
% 3.38/1.00  inst_num_child_elim:                    0
% 3.38/1.00  inst_num_of_dismatching_blockings:      187
% 3.38/1.00  inst_num_of_non_proper_insts:           509
% 3.38/1.00  inst_num_of_duplicates:                 0
% 3.38/1.00  inst_inst_num_from_inst_to_res:         0
% 3.38/1.00  inst_dismatching_checking_time:         0.
% 3.38/1.00  
% 3.38/1.00  ------ Resolution
% 3.38/1.00  
% 3.38/1.00  res_num_of_clauses:                     0
% 3.38/1.00  res_num_in_passive:                     0
% 3.38/1.00  res_num_in_active:                      0
% 3.38/1.00  res_num_of_loops:                       175
% 3.38/1.00  res_forward_subset_subsumed:            37
% 3.38/1.00  res_backward_subset_subsumed:           2
% 3.38/1.00  res_forward_subsumed:                   0
% 3.38/1.00  res_backward_subsumed:                  0
% 3.38/1.00  res_forward_subsumption_resolution:     6
% 3.38/1.00  res_backward_subsumption_resolution:    0
% 3.38/1.00  res_clause_to_clause_subsumption:       358
% 3.38/1.00  res_orphan_elimination:                 0
% 3.38/1.00  res_tautology_del:                      34
% 3.38/1.00  res_num_eq_res_simplified:              1
% 3.38/1.00  res_num_sel_changes:                    0
% 3.38/1.00  res_moves_from_active_to_pass:          0
% 3.38/1.00  
% 3.38/1.00  ------ Superposition
% 3.38/1.00  
% 3.38/1.00  sup_time_total:                         0.
% 3.38/1.00  sup_time_generating:                    0.
% 3.38/1.00  sup_time_sim_full:                      0.
% 3.38/1.00  sup_time_sim_immed:                     0.
% 3.38/1.00  
% 3.38/1.00  sup_num_of_clauses:                     131
% 3.38/1.00  sup_num_in_active:                      56
% 3.38/1.00  sup_num_in_passive:                     75
% 3.38/1.00  sup_num_of_loops:                       89
% 3.38/1.00  sup_fw_superposition:                   101
% 3.38/1.00  sup_bw_superposition:                   59
% 3.38/1.00  sup_immediate_simplified:               49
% 3.38/1.00  sup_given_eliminated:                   0
% 3.38/1.00  comparisons_done:                       0
% 3.38/1.00  comparisons_avoided:                    25
% 3.38/1.00  
% 3.38/1.00  ------ Simplifications
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  sim_fw_subset_subsumed:                 14
% 3.38/1.00  sim_bw_subset_subsumed:                 12
% 3.38/1.00  sim_fw_subsumed:                        6
% 3.38/1.00  sim_bw_subsumed:                        2
% 3.38/1.00  sim_fw_subsumption_res:                 8
% 3.38/1.00  sim_bw_subsumption_res:                 4
% 3.38/1.00  sim_tautology_del:                      5
% 3.38/1.00  sim_eq_tautology_del:                   11
% 3.38/1.00  sim_eq_res_simp:                        3
% 3.38/1.00  sim_fw_demodulated:                     11
% 3.38/1.00  sim_bw_demodulated:                     32
% 3.38/1.00  sim_light_normalised:                   14
% 3.38/1.00  sim_joinable_taut:                      0
% 3.38/1.00  sim_joinable_simp:                      0
% 3.38/1.00  sim_ac_normalised:                      0
% 3.38/1.00  sim_smt_subsumption:                    0
% 3.38/1.00  
%------------------------------------------------------------------------------
