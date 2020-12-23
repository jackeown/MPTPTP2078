%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:59 EST 2020

% Result     : Theorem 47.04s
% Output     : CNFRefutation 47.04s
% Verified   : 
% Statistics : Number of formulae       :  356 (6135 expanded)
%              Number of clauses        :  271 (2495 expanded)
%              Number of leaves         :   24 (1099 expanded)
%              Depth                    :   39
%              Number of atoms          : 1036 (26671 expanded)
%              Number of equality atoms :  635 (8568 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1541,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2669,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1544])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1543,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2254,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1543])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2498,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2254,c_36])).

cnf(c_2672,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2669,c_2498])).

cnf(c_2951,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2672,c_36])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1548,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2403,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1548])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1554,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4011,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2403,c_1554])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1552,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1559,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2328,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1559])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_254])).

cnf(c_1539,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_2495,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_1539])).

cnf(c_2559,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_2495])).

cnf(c_4307,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4011,c_2559])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1557,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1562,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3376,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_1562])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X3,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1546])).

cnf(c_15555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_3880])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1547,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17347,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15555,c_1547])).

cnf(c_33893,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | v4_relat_1(X1,X0) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_17347])).

cnf(c_95249,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_33893])).

cnf(c_2587,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2588,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_16,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4484,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4485,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4484])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1545,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3168,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_1545])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3820,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3168,c_36,c_38])).

cnf(c_3827,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_1559])).

cnf(c_5385,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_1539])).

cnf(c_95985,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_95249,c_2559,c_2588,c_4485,c_5385])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_514,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1534,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_2504,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2498,c_1534])).

cnf(c_95988,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_95985,c_2504])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1542,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_530,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_532,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_33])).

cnf(c_2757,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1541,c_1547])).

cnf(c_2923,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_532,c_2757])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1549,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4000,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_1549])).

cnf(c_5146,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4000,c_2559])).

cnf(c_5147,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5146])).

cnf(c_5154,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1542,c_5147])).

cnf(c_107329,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_95988,c_5154])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_98,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_111,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_862,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1609,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1610,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_1607,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1615,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_861,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1628,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1649,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1685,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK2)
    | r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1640,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X1)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_1699,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_865,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1851,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1852,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1935,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1552])).

cnf(c_1937,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1935])).

cnf(c_2064,plain,
    ( v4_relat_1(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2066,plain,
    ( v4_relat_1(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_2107,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2200,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_2409,plain,
    ( v4_relat_1(sK3,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2403])).

cnf(c_2451,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_2452,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_540,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_623,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_540])).

cnf(c_1533,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_2503,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2498,c_1533])).

cnf(c_2560,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2559])).

cnf(c_2597,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_21,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_435,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_436,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1538,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_1565,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1538,c_2])).

cnf(c_2502,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2498,c_1565])).

cnf(c_1606,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1613,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1622,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1657,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1915,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2359,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_2602,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2502,c_32,c_31,c_110,c_111,c_1613,c_1622,c_1649,c_2359,c_2452])).

cnf(c_2603,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2602])).

cnf(c_2404,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1548])).

cnf(c_2751,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_2404])).

cnf(c_2752,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2751])).

cnf(c_2754,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2752])).

cnf(c_1550,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1561,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2249,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1561])).

cnf(c_3022,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_1935])).

cnf(c_3025,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3022,c_1550])).

cnf(c_3027,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3025])).

cnf(c_1815,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_2312,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X1,sK2)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_3126,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(k1_relat_1(X1),sK2)
    | X0 != k1_relat_1(X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_3128,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | r1_tarski(k1_xboole_0,sK2)
    | sK2 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3126])).

cnf(c_3237,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3239,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_1762,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1983,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_3969,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2767,plain,
    ( v4_relat_1(X0,sK2)
    | ~ r1_tarski(k1_relat_1(X0),sK2)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5283,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_1799,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6177,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_6184,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_6177])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_49317,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_107333,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_107329,c_31,c_98,c_108,c_110,c_111,c_1610,c_1615,c_1628,c_1649,c_1685,c_1699,c_1852,c_1937,c_2066,c_2107,c_2200,c_2409,c_2452,c_2503,c_2560,c_2597,c_2603,c_2754,c_3027,c_3128,c_3239,c_3969,c_5283,c_6184,c_49317])).

cnf(c_107337,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_107333])).

cnf(c_107,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_109,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_875,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_2356,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
    | X2 != X0
    | k1_zfmisc_1(k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_3401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_11260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3401])).

cnf(c_11261,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK2 != X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11260])).

cnf(c_11263,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK2 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11261])).

cnf(c_37752,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5385,c_2588])).

cnf(c_5483,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5154,c_1557])).

cnf(c_5616,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_5483])).

cnf(c_1686,plain,
    ( v4_relat_1(k1_xboole_0,sK2) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_1698,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X0)
    | k1_xboole_0 != X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_1700,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_2065,plain,
    ( v4_relat_1(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2064])).

cnf(c_2067,plain,
    ( v4_relat_1(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_3127,plain,
    ( X0 != k1_relat_1(X1)
    | sK2 != sK2
    | r1_tarski(X0,sK2) = iProver_top
    | r1_tarski(k1_relat_1(X1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3126])).

cnf(c_3129,plain,
    ( sK2 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),sK2) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_6650,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(sK2,sK2)
    | sK2 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_6653,plain,
    ( sK2 != X0
    | sK2 != sK2
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6650])).

cnf(c_6655,plain,
    ( sK2 != sK2
    | sK2 != k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6653])).

cnf(c_41670,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5616,c_98,c_109,c_110,c_111,c_1649,c_1686,c_1700,c_1852,c_1935,c_1937,c_2067,c_2107,c_2603,c_2754,c_3025,c_3027,c_3129,c_3239,c_6655])).

cnf(c_41675,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_37752,c_41670])).

cnf(c_47420,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_53693,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_47420])).

cnf(c_60560,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_53693])).

cnf(c_60561,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60560])).

cnf(c_1551,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4315,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_1551])).

cnf(c_7049,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4315,c_2588,c_5385])).

cnf(c_7053,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7049,c_1550])).

cnf(c_12237,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7053,c_2588,c_5385])).

cnf(c_3885,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1546])).

cnf(c_5267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3885,c_1559])).

cnf(c_1889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1890,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_15564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3880])).

cnf(c_97,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2353,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2354,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_3617,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_1539])).

cnf(c_7524,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_2588])).

cnf(c_7525,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7524])).

cnf(c_3275,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1561])).

cnf(c_7236,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_3275])).

cnf(c_5391,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5385])).

cnf(c_7430,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7236,c_2588,c_5391])).

cnf(c_3883,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_1546])).

cnf(c_8029,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3883])).

cnf(c_8291,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7430,c_8029])).

cnf(c_4015,plain,
    ( v4_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4011])).

cnf(c_8290,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_8029])).

cnf(c_8296,plain,
    ( v4_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8290])).

cnf(c_9138,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8291,c_2559,c_2588,c_4015,c_5391,c_8296])).

cnf(c_9142,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9138,c_1559])).

cnf(c_9327,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9142,c_1561])).

cnf(c_9338,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9327,c_1550])).

cnf(c_10424,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9338,c_2559])).

cnf(c_10429,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10424,c_1562])).

cnf(c_15590,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15564,c_97,c_2354,c_2751,c_3885,c_7525,c_10429])).

cnf(c_15591,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15590])).

cnf(c_15598,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15591,c_1559])).

cnf(c_34244,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5267,c_1890,c_15598])).

cnf(c_34245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_34244])).

cnf(c_1558,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_34257,plain,
    ( v4_relat_1(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_34245,c_1558])).

cnf(c_36331,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5154,c_34257])).

cnf(c_1654,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1655,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_8292,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5154,c_8029])).

cnf(c_8540,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8292,c_1559])).

cnf(c_13165,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8540,c_1539])).

cnf(c_36564,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36331,c_1655,c_1935,c_13165])).

cnf(c_36565,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36564])).

cnf(c_36570,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_36565])).

cnf(c_8030,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(X1,sK1)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_1559])).

cnf(c_14814,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_8030])).

cnf(c_14834,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_14814])).

cnf(c_46164,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14834,c_2588,c_5385])).

cnf(c_46165,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_46164])).

cnf(c_46172,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36570,c_46165])).

cnf(c_46190,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_46172,c_1562])).

cnf(c_4266,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,X2)
    | X2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_4267,plain,
    ( X0 != X1
    | sK0 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4266])).

cnf(c_4269,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4267])).

cnf(c_13164,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8540,c_1562])).

cnf(c_15772,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15598,c_1562])).

cnf(c_21946,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_15772])).

cnf(c_22040,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21946,c_1562])).

cnf(c_22570,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_22040])).

cnf(c_22941,plain,
    ( v4_relat_1(X0,sK2) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_22570])).

cnf(c_14816,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,sK1)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8030,c_1562])).

cnf(c_65586,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
    | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
    | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22941,c_14816])).

cnf(c_65796,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
    | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
    | r1_tarski(X1,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65586,c_3])).

cnf(c_66326,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(X1,k1_xboole_0) = iProver_top
    | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
    | v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_65796,c_2588,c_5385])).

cnf(c_66327,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
    | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
    | r1_tarski(X1,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_66326])).

cnf(c_66331,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_66327])).

cnf(c_71242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46190,c_31,c_110,c_111,c_1615,c_1628,c_1655,c_1935,c_2452,c_3025,c_4269,c_13164,c_66331])).

cnf(c_71252,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12237,c_71242])).

cnf(c_107339,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15591,c_107333])).

cnf(c_107341,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_107333])).

cnf(c_107770,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_107337,c_109,c_110,c_111,c_875,c_1649,c_1935,c_2603,c_3025,c_5154,c_11263,c_41675,c_60561,c_71252,c_107339,c_107341])).

cnf(c_107774,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2951,c_107770])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:14:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 47.04/6.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.04/6.48  
% 47.04/6.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.04/6.48  
% 47.04/6.48  ------  iProver source info
% 47.04/6.48  
% 47.04/6.48  git: date: 2020-06-30 10:37:57 +0100
% 47.04/6.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.04/6.48  git: non_committed_changes: false
% 47.04/6.48  git: last_make_outside_of_git: false
% 47.04/6.48  
% 47.04/6.48  ------ 
% 47.04/6.48  
% 47.04/6.48  ------ Input Options
% 47.04/6.48  
% 47.04/6.48  --out_options                           all
% 47.04/6.48  --tptp_safe_out                         true
% 47.04/6.48  --problem_path                          ""
% 47.04/6.48  --include_path                          ""
% 47.04/6.48  --clausifier                            res/vclausify_rel
% 47.04/6.48  --clausifier_options                    ""
% 47.04/6.48  --stdin                                 false
% 47.04/6.48  --stats_out                             all
% 47.04/6.48  
% 47.04/6.48  ------ General Options
% 47.04/6.48  
% 47.04/6.48  --fof                                   false
% 47.04/6.48  --time_out_real                         305.
% 47.04/6.48  --time_out_virtual                      -1.
% 47.04/6.48  --symbol_type_check                     false
% 47.04/6.48  --clausify_out                          false
% 47.04/6.48  --sig_cnt_out                           false
% 47.04/6.48  --trig_cnt_out                          false
% 47.04/6.48  --trig_cnt_out_tolerance                1.
% 47.04/6.48  --trig_cnt_out_sk_spl                   false
% 47.04/6.48  --abstr_cl_out                          false
% 47.04/6.48  
% 47.04/6.48  ------ Global Options
% 47.04/6.48  
% 47.04/6.48  --schedule                              default
% 47.04/6.48  --add_important_lit                     false
% 47.04/6.48  --prop_solver_per_cl                    1000
% 47.04/6.48  --min_unsat_core                        false
% 47.04/6.48  --soft_assumptions                      false
% 47.04/6.48  --soft_lemma_size                       3
% 47.04/6.48  --prop_impl_unit_size                   0
% 47.04/6.48  --prop_impl_unit                        []
% 47.04/6.48  --share_sel_clauses                     true
% 47.04/6.48  --reset_solvers                         false
% 47.04/6.48  --bc_imp_inh                            [conj_cone]
% 47.04/6.48  --conj_cone_tolerance                   3.
% 47.04/6.48  --extra_neg_conj                        none
% 47.04/6.48  --large_theory_mode                     true
% 47.04/6.48  --prolific_symb_bound                   200
% 47.04/6.48  --lt_threshold                          2000
% 47.04/6.48  --clause_weak_htbl                      true
% 47.04/6.48  --gc_record_bc_elim                     false
% 47.04/6.48  
% 47.04/6.48  ------ Preprocessing Options
% 47.04/6.48  
% 47.04/6.48  --preprocessing_flag                    true
% 47.04/6.48  --time_out_prep_mult                    0.1
% 47.04/6.48  --splitting_mode                        input
% 47.04/6.48  --splitting_grd                         true
% 47.04/6.48  --splitting_cvd                         false
% 47.04/6.48  --splitting_cvd_svl                     false
% 47.04/6.48  --splitting_nvd                         32
% 47.04/6.48  --sub_typing                            true
% 47.04/6.48  --prep_gs_sim                           true
% 47.04/6.48  --prep_unflatten                        true
% 47.04/6.48  --prep_res_sim                          true
% 47.04/6.48  --prep_upred                            true
% 47.04/6.48  --prep_sem_filter                       exhaustive
% 47.04/6.48  --prep_sem_filter_out                   false
% 47.04/6.48  --pred_elim                             true
% 47.04/6.48  --res_sim_input                         true
% 47.04/6.48  --eq_ax_congr_red                       true
% 47.04/6.48  --pure_diseq_elim                       true
% 47.04/6.48  --brand_transform                       false
% 47.04/6.48  --non_eq_to_eq                          false
% 47.04/6.48  --prep_def_merge                        true
% 47.04/6.48  --prep_def_merge_prop_impl              false
% 47.04/6.48  --prep_def_merge_mbd                    true
% 47.04/6.48  --prep_def_merge_tr_red                 false
% 47.04/6.48  --prep_def_merge_tr_cl                  false
% 47.04/6.48  --smt_preprocessing                     true
% 47.04/6.48  --smt_ac_axioms                         fast
% 47.04/6.48  --preprocessed_out                      false
% 47.04/6.48  --preprocessed_stats                    false
% 47.04/6.48  
% 47.04/6.48  ------ Abstraction refinement Options
% 47.04/6.48  
% 47.04/6.48  --abstr_ref                             []
% 47.04/6.48  --abstr_ref_prep                        false
% 47.04/6.48  --abstr_ref_until_sat                   false
% 47.04/6.48  --abstr_ref_sig_restrict                funpre
% 47.04/6.48  --abstr_ref_af_restrict_to_split_sk     false
% 47.04/6.48  --abstr_ref_under                       []
% 47.04/6.48  
% 47.04/6.48  ------ SAT Options
% 47.04/6.48  
% 47.04/6.48  --sat_mode                              false
% 47.04/6.48  --sat_fm_restart_options                ""
% 47.04/6.48  --sat_gr_def                            false
% 47.04/6.48  --sat_epr_types                         true
% 47.04/6.48  --sat_non_cyclic_types                  false
% 47.04/6.48  --sat_finite_models                     false
% 47.04/6.48  --sat_fm_lemmas                         false
% 47.04/6.48  --sat_fm_prep                           false
% 47.04/6.48  --sat_fm_uc_incr                        true
% 47.04/6.48  --sat_out_model                         small
% 47.04/6.48  --sat_out_clauses                       false
% 47.04/6.48  
% 47.04/6.48  ------ QBF Options
% 47.04/6.48  
% 47.04/6.48  --qbf_mode                              false
% 47.04/6.48  --qbf_elim_univ                         false
% 47.04/6.48  --qbf_dom_inst                          none
% 47.04/6.48  --qbf_dom_pre_inst                      false
% 47.04/6.48  --qbf_sk_in                             false
% 47.04/6.48  --qbf_pred_elim                         true
% 47.04/6.48  --qbf_split                             512
% 47.04/6.48  
% 47.04/6.48  ------ BMC1 Options
% 47.04/6.48  
% 47.04/6.48  --bmc1_incremental                      false
% 47.04/6.48  --bmc1_axioms                           reachable_all
% 47.04/6.48  --bmc1_min_bound                        0
% 47.04/6.48  --bmc1_max_bound                        -1
% 47.04/6.48  --bmc1_max_bound_default                -1
% 47.04/6.48  --bmc1_symbol_reachability              true
% 47.04/6.48  --bmc1_property_lemmas                  false
% 47.04/6.48  --bmc1_k_induction                      false
% 47.04/6.48  --bmc1_non_equiv_states                 false
% 47.04/6.48  --bmc1_deadlock                         false
% 47.04/6.48  --bmc1_ucm                              false
% 47.04/6.48  --bmc1_add_unsat_core                   none
% 47.04/6.48  --bmc1_unsat_core_children              false
% 47.04/6.48  --bmc1_unsat_core_extrapolate_axioms    false
% 47.04/6.48  --bmc1_out_stat                         full
% 47.04/6.48  --bmc1_ground_init                      false
% 47.04/6.48  --bmc1_pre_inst_next_state              false
% 47.04/6.48  --bmc1_pre_inst_state                   false
% 47.04/6.48  --bmc1_pre_inst_reach_state             false
% 47.04/6.48  --bmc1_out_unsat_core                   false
% 47.04/6.48  --bmc1_aig_witness_out                  false
% 47.04/6.48  --bmc1_verbose                          false
% 47.04/6.48  --bmc1_dump_clauses_tptp                false
% 47.04/6.48  --bmc1_dump_unsat_core_tptp             false
% 47.04/6.48  --bmc1_dump_file                        -
% 47.04/6.48  --bmc1_ucm_expand_uc_limit              128
% 47.04/6.48  --bmc1_ucm_n_expand_iterations          6
% 47.04/6.48  --bmc1_ucm_extend_mode                  1
% 47.04/6.48  --bmc1_ucm_init_mode                    2
% 47.04/6.48  --bmc1_ucm_cone_mode                    none
% 47.04/6.48  --bmc1_ucm_reduced_relation_type        0
% 47.04/6.48  --bmc1_ucm_relax_model                  4
% 47.04/6.48  --bmc1_ucm_full_tr_after_sat            true
% 47.04/6.48  --bmc1_ucm_expand_neg_assumptions       false
% 47.04/6.48  --bmc1_ucm_layered_model                none
% 47.04/6.49  --bmc1_ucm_max_lemma_size               10
% 47.04/6.49  
% 47.04/6.49  ------ AIG Options
% 47.04/6.49  
% 47.04/6.49  --aig_mode                              false
% 47.04/6.49  
% 47.04/6.49  ------ Instantiation Options
% 47.04/6.49  
% 47.04/6.49  --instantiation_flag                    true
% 47.04/6.49  --inst_sos_flag                         true
% 47.04/6.49  --inst_sos_phase                        true
% 47.04/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.04/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.04/6.49  --inst_lit_sel_side                     num_symb
% 47.04/6.49  --inst_solver_per_active                1400
% 47.04/6.49  --inst_solver_calls_frac                1.
% 47.04/6.49  --inst_passive_queue_type               priority_queues
% 47.04/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.04/6.49  --inst_passive_queues_freq              [25;2]
% 47.04/6.49  --inst_dismatching                      true
% 47.04/6.49  --inst_eager_unprocessed_to_passive     true
% 47.04/6.49  --inst_prop_sim_given                   true
% 47.04/6.49  --inst_prop_sim_new                     false
% 47.04/6.49  --inst_subs_new                         false
% 47.04/6.49  --inst_eq_res_simp                      false
% 47.04/6.49  --inst_subs_given                       false
% 47.04/6.49  --inst_orphan_elimination               true
% 47.04/6.49  --inst_learning_loop_flag               true
% 47.04/6.49  --inst_learning_start                   3000
% 47.04/6.49  --inst_learning_factor                  2
% 47.04/6.49  --inst_start_prop_sim_after_learn       3
% 47.04/6.49  --inst_sel_renew                        solver
% 47.04/6.49  --inst_lit_activity_flag                true
% 47.04/6.49  --inst_restr_to_given                   false
% 47.04/6.49  --inst_activity_threshold               500
% 47.04/6.49  --inst_out_proof                        true
% 47.04/6.49  
% 47.04/6.49  ------ Resolution Options
% 47.04/6.49  
% 47.04/6.49  --resolution_flag                       true
% 47.04/6.49  --res_lit_sel                           adaptive
% 47.04/6.49  --res_lit_sel_side                      none
% 47.04/6.49  --res_ordering                          kbo
% 47.04/6.49  --res_to_prop_solver                    active
% 47.04/6.49  --res_prop_simpl_new                    false
% 47.04/6.49  --res_prop_simpl_given                  true
% 47.04/6.49  --res_passive_queue_type                priority_queues
% 47.04/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.04/6.49  --res_passive_queues_freq               [15;5]
% 47.04/6.49  --res_forward_subs                      full
% 47.04/6.49  --res_backward_subs                     full
% 47.04/6.49  --res_forward_subs_resolution           true
% 47.04/6.49  --res_backward_subs_resolution          true
% 47.04/6.49  --res_orphan_elimination                true
% 47.04/6.49  --res_time_limit                        2.
% 47.04/6.49  --res_out_proof                         true
% 47.04/6.49  
% 47.04/6.49  ------ Superposition Options
% 47.04/6.49  
% 47.04/6.49  --superposition_flag                    true
% 47.04/6.49  --sup_passive_queue_type                priority_queues
% 47.04/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.04/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.04/6.49  --demod_completeness_check              fast
% 47.04/6.49  --demod_use_ground                      true
% 47.04/6.49  --sup_to_prop_solver                    passive
% 47.04/6.49  --sup_prop_simpl_new                    true
% 47.04/6.49  --sup_prop_simpl_given                  true
% 47.04/6.49  --sup_fun_splitting                     true
% 47.04/6.49  --sup_smt_interval                      50000
% 47.04/6.49  
% 47.04/6.49  ------ Superposition Simplification Setup
% 47.04/6.49  
% 47.04/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.04/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.04/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.04/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.04/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.04/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.04/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.04/6.49  --sup_immed_triv                        [TrivRules]
% 47.04/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_immed_bw_main                     []
% 47.04/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.04/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.04/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_input_bw                          []
% 47.04/6.49  
% 47.04/6.49  ------ Combination Options
% 47.04/6.49  
% 47.04/6.49  --comb_res_mult                         3
% 47.04/6.49  --comb_sup_mult                         2
% 47.04/6.49  --comb_inst_mult                        10
% 47.04/6.49  
% 47.04/6.49  ------ Debug Options
% 47.04/6.49  
% 47.04/6.49  --dbg_backtrace                         false
% 47.04/6.49  --dbg_dump_prop_clauses                 false
% 47.04/6.49  --dbg_dump_prop_clauses_file            -
% 47.04/6.49  --dbg_out_stat                          false
% 47.04/6.49  ------ Parsing...
% 47.04/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.04/6.49  
% 47.04/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 47.04/6.49  
% 47.04/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.04/6.49  
% 47.04/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.04/6.49  ------ Proving...
% 47.04/6.49  ------ Problem Properties 
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  clauses                                 35
% 47.04/6.49  conjectures                             4
% 47.04/6.49  EPR                                     6
% 47.04/6.49  Horn                                    32
% 47.04/6.49  unary                                   6
% 47.04/6.49  binary                                  9
% 47.04/6.49  lits                                    92
% 47.04/6.49  lits eq                                 28
% 47.04/6.49  fd_pure                                 0
% 47.04/6.49  fd_pseudo                               0
% 47.04/6.49  fd_cond                                 2
% 47.04/6.49  fd_pseudo_cond                          0
% 47.04/6.49  AC symbols                              0
% 47.04/6.49  
% 47.04/6.49  ------ Schedule dynamic 5 is on 
% 47.04/6.49  
% 47.04/6.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  ------ 
% 47.04/6.49  Current options:
% 47.04/6.49  ------ 
% 47.04/6.49  
% 47.04/6.49  ------ Input Options
% 47.04/6.49  
% 47.04/6.49  --out_options                           all
% 47.04/6.49  --tptp_safe_out                         true
% 47.04/6.49  --problem_path                          ""
% 47.04/6.49  --include_path                          ""
% 47.04/6.49  --clausifier                            res/vclausify_rel
% 47.04/6.49  --clausifier_options                    ""
% 47.04/6.49  --stdin                                 false
% 47.04/6.49  --stats_out                             all
% 47.04/6.49  
% 47.04/6.49  ------ General Options
% 47.04/6.49  
% 47.04/6.49  --fof                                   false
% 47.04/6.49  --time_out_real                         305.
% 47.04/6.49  --time_out_virtual                      -1.
% 47.04/6.49  --symbol_type_check                     false
% 47.04/6.49  --clausify_out                          false
% 47.04/6.49  --sig_cnt_out                           false
% 47.04/6.49  --trig_cnt_out                          false
% 47.04/6.49  --trig_cnt_out_tolerance                1.
% 47.04/6.49  --trig_cnt_out_sk_spl                   false
% 47.04/6.49  --abstr_cl_out                          false
% 47.04/6.49  
% 47.04/6.49  ------ Global Options
% 47.04/6.49  
% 47.04/6.49  --schedule                              default
% 47.04/6.49  --add_important_lit                     false
% 47.04/6.49  --prop_solver_per_cl                    1000
% 47.04/6.49  --min_unsat_core                        false
% 47.04/6.49  --soft_assumptions                      false
% 47.04/6.49  --soft_lemma_size                       3
% 47.04/6.49  --prop_impl_unit_size                   0
% 47.04/6.49  --prop_impl_unit                        []
% 47.04/6.49  --share_sel_clauses                     true
% 47.04/6.49  --reset_solvers                         false
% 47.04/6.49  --bc_imp_inh                            [conj_cone]
% 47.04/6.49  --conj_cone_tolerance                   3.
% 47.04/6.49  --extra_neg_conj                        none
% 47.04/6.49  --large_theory_mode                     true
% 47.04/6.49  --prolific_symb_bound                   200
% 47.04/6.49  --lt_threshold                          2000
% 47.04/6.49  --clause_weak_htbl                      true
% 47.04/6.49  --gc_record_bc_elim                     false
% 47.04/6.49  
% 47.04/6.49  ------ Preprocessing Options
% 47.04/6.49  
% 47.04/6.49  --preprocessing_flag                    true
% 47.04/6.49  --time_out_prep_mult                    0.1
% 47.04/6.49  --splitting_mode                        input
% 47.04/6.49  --splitting_grd                         true
% 47.04/6.49  --splitting_cvd                         false
% 47.04/6.49  --splitting_cvd_svl                     false
% 47.04/6.49  --splitting_nvd                         32
% 47.04/6.49  --sub_typing                            true
% 47.04/6.49  --prep_gs_sim                           true
% 47.04/6.49  --prep_unflatten                        true
% 47.04/6.49  --prep_res_sim                          true
% 47.04/6.49  --prep_upred                            true
% 47.04/6.49  --prep_sem_filter                       exhaustive
% 47.04/6.49  --prep_sem_filter_out                   false
% 47.04/6.49  --pred_elim                             true
% 47.04/6.49  --res_sim_input                         true
% 47.04/6.49  --eq_ax_congr_red                       true
% 47.04/6.49  --pure_diseq_elim                       true
% 47.04/6.49  --brand_transform                       false
% 47.04/6.49  --non_eq_to_eq                          false
% 47.04/6.49  --prep_def_merge                        true
% 47.04/6.49  --prep_def_merge_prop_impl              false
% 47.04/6.49  --prep_def_merge_mbd                    true
% 47.04/6.49  --prep_def_merge_tr_red                 false
% 47.04/6.49  --prep_def_merge_tr_cl                  false
% 47.04/6.49  --smt_preprocessing                     true
% 47.04/6.49  --smt_ac_axioms                         fast
% 47.04/6.49  --preprocessed_out                      false
% 47.04/6.49  --preprocessed_stats                    false
% 47.04/6.49  
% 47.04/6.49  ------ Abstraction refinement Options
% 47.04/6.49  
% 47.04/6.49  --abstr_ref                             []
% 47.04/6.49  --abstr_ref_prep                        false
% 47.04/6.49  --abstr_ref_until_sat                   false
% 47.04/6.49  --abstr_ref_sig_restrict                funpre
% 47.04/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.04/6.49  --abstr_ref_under                       []
% 47.04/6.49  
% 47.04/6.49  ------ SAT Options
% 47.04/6.49  
% 47.04/6.49  --sat_mode                              false
% 47.04/6.49  --sat_fm_restart_options                ""
% 47.04/6.49  --sat_gr_def                            false
% 47.04/6.49  --sat_epr_types                         true
% 47.04/6.49  --sat_non_cyclic_types                  false
% 47.04/6.49  --sat_finite_models                     false
% 47.04/6.49  --sat_fm_lemmas                         false
% 47.04/6.49  --sat_fm_prep                           false
% 47.04/6.49  --sat_fm_uc_incr                        true
% 47.04/6.49  --sat_out_model                         small
% 47.04/6.49  --sat_out_clauses                       false
% 47.04/6.49  
% 47.04/6.49  ------ QBF Options
% 47.04/6.49  
% 47.04/6.49  --qbf_mode                              false
% 47.04/6.49  --qbf_elim_univ                         false
% 47.04/6.49  --qbf_dom_inst                          none
% 47.04/6.49  --qbf_dom_pre_inst                      false
% 47.04/6.49  --qbf_sk_in                             false
% 47.04/6.49  --qbf_pred_elim                         true
% 47.04/6.49  --qbf_split                             512
% 47.04/6.49  
% 47.04/6.49  ------ BMC1 Options
% 47.04/6.49  
% 47.04/6.49  --bmc1_incremental                      false
% 47.04/6.49  --bmc1_axioms                           reachable_all
% 47.04/6.49  --bmc1_min_bound                        0
% 47.04/6.49  --bmc1_max_bound                        -1
% 47.04/6.49  --bmc1_max_bound_default                -1
% 47.04/6.49  --bmc1_symbol_reachability              true
% 47.04/6.49  --bmc1_property_lemmas                  false
% 47.04/6.49  --bmc1_k_induction                      false
% 47.04/6.49  --bmc1_non_equiv_states                 false
% 47.04/6.49  --bmc1_deadlock                         false
% 47.04/6.49  --bmc1_ucm                              false
% 47.04/6.49  --bmc1_add_unsat_core                   none
% 47.04/6.49  --bmc1_unsat_core_children              false
% 47.04/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.04/6.49  --bmc1_out_stat                         full
% 47.04/6.49  --bmc1_ground_init                      false
% 47.04/6.49  --bmc1_pre_inst_next_state              false
% 47.04/6.49  --bmc1_pre_inst_state                   false
% 47.04/6.49  --bmc1_pre_inst_reach_state             false
% 47.04/6.49  --bmc1_out_unsat_core                   false
% 47.04/6.49  --bmc1_aig_witness_out                  false
% 47.04/6.49  --bmc1_verbose                          false
% 47.04/6.49  --bmc1_dump_clauses_tptp                false
% 47.04/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.04/6.49  --bmc1_dump_file                        -
% 47.04/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.04/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.04/6.49  --bmc1_ucm_extend_mode                  1
% 47.04/6.49  --bmc1_ucm_init_mode                    2
% 47.04/6.49  --bmc1_ucm_cone_mode                    none
% 47.04/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.04/6.49  --bmc1_ucm_relax_model                  4
% 47.04/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.04/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.04/6.49  --bmc1_ucm_layered_model                none
% 47.04/6.49  --bmc1_ucm_max_lemma_size               10
% 47.04/6.49  
% 47.04/6.49  ------ AIG Options
% 47.04/6.49  
% 47.04/6.49  --aig_mode                              false
% 47.04/6.49  
% 47.04/6.49  ------ Instantiation Options
% 47.04/6.49  
% 47.04/6.49  --instantiation_flag                    true
% 47.04/6.49  --inst_sos_flag                         true
% 47.04/6.49  --inst_sos_phase                        true
% 47.04/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.04/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.04/6.49  --inst_lit_sel_side                     none
% 47.04/6.49  --inst_solver_per_active                1400
% 47.04/6.49  --inst_solver_calls_frac                1.
% 47.04/6.49  --inst_passive_queue_type               priority_queues
% 47.04/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.04/6.49  --inst_passive_queues_freq              [25;2]
% 47.04/6.49  --inst_dismatching                      true
% 47.04/6.49  --inst_eager_unprocessed_to_passive     true
% 47.04/6.49  --inst_prop_sim_given                   true
% 47.04/6.49  --inst_prop_sim_new                     false
% 47.04/6.49  --inst_subs_new                         false
% 47.04/6.49  --inst_eq_res_simp                      false
% 47.04/6.49  --inst_subs_given                       false
% 47.04/6.49  --inst_orphan_elimination               true
% 47.04/6.49  --inst_learning_loop_flag               true
% 47.04/6.49  --inst_learning_start                   3000
% 47.04/6.49  --inst_learning_factor                  2
% 47.04/6.49  --inst_start_prop_sim_after_learn       3
% 47.04/6.49  --inst_sel_renew                        solver
% 47.04/6.49  --inst_lit_activity_flag                true
% 47.04/6.49  --inst_restr_to_given                   false
% 47.04/6.49  --inst_activity_threshold               500
% 47.04/6.49  --inst_out_proof                        true
% 47.04/6.49  
% 47.04/6.49  ------ Resolution Options
% 47.04/6.49  
% 47.04/6.49  --resolution_flag                       false
% 47.04/6.49  --res_lit_sel                           adaptive
% 47.04/6.49  --res_lit_sel_side                      none
% 47.04/6.49  --res_ordering                          kbo
% 47.04/6.49  --res_to_prop_solver                    active
% 47.04/6.49  --res_prop_simpl_new                    false
% 47.04/6.49  --res_prop_simpl_given                  true
% 47.04/6.49  --res_passive_queue_type                priority_queues
% 47.04/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.04/6.49  --res_passive_queues_freq               [15;5]
% 47.04/6.49  --res_forward_subs                      full
% 47.04/6.49  --res_backward_subs                     full
% 47.04/6.49  --res_forward_subs_resolution           true
% 47.04/6.49  --res_backward_subs_resolution          true
% 47.04/6.49  --res_orphan_elimination                true
% 47.04/6.49  --res_time_limit                        2.
% 47.04/6.49  --res_out_proof                         true
% 47.04/6.49  
% 47.04/6.49  ------ Superposition Options
% 47.04/6.49  
% 47.04/6.49  --superposition_flag                    true
% 47.04/6.49  --sup_passive_queue_type                priority_queues
% 47.04/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.04/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.04/6.49  --demod_completeness_check              fast
% 47.04/6.49  --demod_use_ground                      true
% 47.04/6.49  --sup_to_prop_solver                    passive
% 47.04/6.49  --sup_prop_simpl_new                    true
% 47.04/6.49  --sup_prop_simpl_given                  true
% 47.04/6.49  --sup_fun_splitting                     true
% 47.04/6.49  --sup_smt_interval                      50000
% 47.04/6.49  
% 47.04/6.49  ------ Superposition Simplification Setup
% 47.04/6.49  
% 47.04/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.04/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.04/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.04/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.04/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.04/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.04/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.04/6.49  --sup_immed_triv                        [TrivRules]
% 47.04/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_immed_bw_main                     []
% 47.04/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.04/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.04/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.04/6.49  --sup_input_bw                          []
% 47.04/6.49  
% 47.04/6.49  ------ Combination Options
% 47.04/6.49  
% 47.04/6.49  --comb_res_mult                         3
% 47.04/6.49  --comb_sup_mult                         2
% 47.04/6.49  --comb_inst_mult                        10
% 47.04/6.49  
% 47.04/6.49  ------ Debug Options
% 47.04/6.49  
% 47.04/6.49  --dbg_backtrace                         false
% 47.04/6.49  --dbg_dump_prop_clauses                 false
% 47.04/6.49  --dbg_dump_prop_clauses_file            -
% 47.04/6.49  --dbg_out_stat                          false
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  ------ Proving...
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  % SZS status Theorem for theBenchmark.p
% 47.04/6.49  
% 47.04/6.49   Resolution empty clause
% 47.04/6.49  
% 47.04/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.04/6.49  
% 47.04/6.49  fof(f19,conjecture,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f20,negated_conjecture,(
% 47.04/6.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 47.04/6.49    inference(negated_conjecture,[],[f19])).
% 47.04/6.49  
% 47.04/6.49  fof(f45,plain,(
% 47.04/6.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 47.04/6.49    inference(ennf_transformation,[],[f20])).
% 47.04/6.49  
% 47.04/6.49  fof(f46,plain,(
% 47.04/6.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 47.04/6.49    inference(flattening,[],[f45])).
% 47.04/6.49  
% 47.04/6.49  fof(f52,plain,(
% 47.04/6.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 47.04/6.49    introduced(choice_axiom,[])).
% 47.04/6.49  
% 47.04/6.49  fof(f53,plain,(
% 47.04/6.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 47.04/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f52])).
% 47.04/6.49  
% 47.04/6.49  fof(f86,plain,(
% 47.04/6.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f17,axiom,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f41,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 47.04/6.49    inference(ennf_transformation,[],[f17])).
% 47.04/6.49  
% 47.04/6.49  fof(f42,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 47.04/6.49    inference(flattening,[],[f41])).
% 47.04/6.49  
% 47.04/6.49  fof(f81,plain,(
% 47.04/6.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f42])).
% 47.04/6.49  
% 47.04/6.49  fof(f18,axiom,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f43,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 47.04/6.49    inference(ennf_transformation,[],[f18])).
% 47.04/6.49  
% 47.04/6.49  fof(f44,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 47.04/6.49    inference(flattening,[],[f43])).
% 47.04/6.49  
% 47.04/6.49  fof(f83,plain,(
% 47.04/6.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f44])).
% 47.04/6.49  
% 47.04/6.49  fof(f84,plain,(
% 47.04/6.49    v1_funct_1(sK3)),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f4,axiom,(
% 47.04/6.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f49,plain,(
% 47.04/6.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.04/6.49    inference(nnf_transformation,[],[f4])).
% 47.04/6.49  
% 47.04/6.49  fof(f60,plain,(
% 47.04/6.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f49])).
% 47.04/6.49  
% 47.04/6.49  fof(f13,axiom,(
% 47.04/6.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f21,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 47.04/6.49    inference(pure_predicate_removal,[],[f13])).
% 47.04/6.49  
% 47.04/6.49  fof(f35,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.04/6.49    inference(ennf_transformation,[],[f21])).
% 47.04/6.49  
% 47.04/6.49  fof(f72,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f35])).
% 47.04/6.49  
% 47.04/6.49  fof(f8,axiom,(
% 47.04/6.49    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f28,plain,(
% 47.04/6.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 47.04/6.49    inference(ennf_transformation,[],[f8])).
% 47.04/6.49  
% 47.04/6.49  fof(f29,plain,(
% 47.04/6.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 47.04/6.49    inference(flattening,[],[f28])).
% 47.04/6.49  
% 47.04/6.49  fof(f66,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f29])).
% 47.04/6.49  
% 47.04/6.49  fof(f9,axiom,(
% 47.04/6.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f68,plain,(
% 47.04/6.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f9])).
% 47.04/6.49  
% 47.04/6.49  fof(f59,plain,(
% 47.04/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f49])).
% 47.04/6.49  
% 47.04/6.49  fof(f5,axiom,(
% 47.04/6.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f25,plain,(
% 47.04/6.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 47.04/6.49    inference(ennf_transformation,[],[f5])).
% 47.04/6.49  
% 47.04/6.49  fof(f61,plain,(
% 47.04/6.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f25])).
% 47.04/6.49  
% 47.04/6.49  fof(f6,axiom,(
% 47.04/6.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f26,plain,(
% 47.04/6.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(ennf_transformation,[],[f6])).
% 47.04/6.49  
% 47.04/6.49  fof(f50,plain,(
% 47.04/6.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(nnf_transformation,[],[f26])).
% 47.04/6.49  
% 47.04/6.49  fof(f62,plain,(
% 47.04/6.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f50])).
% 47.04/6.49  
% 47.04/6.49  fof(f1,axiom,(
% 47.04/6.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f22,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 47.04/6.49    inference(ennf_transformation,[],[f1])).
% 47.04/6.49  
% 47.04/6.49  fof(f23,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 47.04/6.49    inference(flattening,[],[f22])).
% 47.04/6.49  
% 47.04/6.49  fof(f54,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f23])).
% 47.04/6.49  
% 47.04/6.49  fof(f15,axiom,(
% 47.04/6.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f37,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 47.04/6.49    inference(ennf_transformation,[],[f15])).
% 47.04/6.49  
% 47.04/6.49  fof(f38,plain,(
% 47.04/6.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 47.04/6.49    inference(flattening,[],[f37])).
% 47.04/6.49  
% 47.04/6.49  fof(f74,plain,(
% 47.04/6.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f38])).
% 47.04/6.49  
% 47.04/6.49  fof(f14,axiom,(
% 47.04/6.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f36,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.04/6.49    inference(ennf_transformation,[],[f14])).
% 47.04/6.49  
% 47.04/6.49  fof(f73,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f36])).
% 47.04/6.49  
% 47.04/6.49  fof(f11,axiom,(
% 47.04/6.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f32,plain,(
% 47.04/6.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(ennf_transformation,[],[f11])).
% 47.04/6.49  
% 47.04/6.49  fof(f70,plain,(
% 47.04/6.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f32])).
% 47.04/6.49  
% 47.04/6.49  fof(f82,plain,(
% 47.04/6.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f42])).
% 47.04/6.49  
% 47.04/6.49  fof(f16,axiom,(
% 47.04/6.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f39,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.04/6.49    inference(ennf_transformation,[],[f16])).
% 47.04/6.49  
% 47.04/6.49  fof(f40,plain,(
% 47.04/6.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.04/6.49    inference(flattening,[],[f39])).
% 47.04/6.49  
% 47.04/6.49  fof(f51,plain,(
% 47.04/6.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.04/6.49    inference(nnf_transformation,[],[f40])).
% 47.04/6.49  
% 47.04/6.49  fof(f77,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f51])).
% 47.04/6.49  
% 47.04/6.49  fof(f89,plain,(
% 47.04/6.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f87,plain,(
% 47.04/6.49    r1_tarski(sK2,sK0)),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f75,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f51])).
% 47.04/6.49  
% 47.04/6.49  fof(f85,plain,(
% 47.04/6.49    v1_funct_2(sK3,sK0,sK1)),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f12,axiom,(
% 47.04/6.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f33,plain,(
% 47.04/6.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(ennf_transformation,[],[f12])).
% 47.04/6.49  
% 47.04/6.49  fof(f34,plain,(
% 47.04/6.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(flattening,[],[f33])).
% 47.04/6.49  
% 47.04/6.49  fof(f71,plain,(
% 47.04/6.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f34])).
% 47.04/6.49  
% 47.04/6.49  fof(f88,plain,(
% 47.04/6.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 47.04/6.49    inference(cnf_transformation,[],[f53])).
% 47.04/6.49  
% 47.04/6.49  fof(f3,axiom,(
% 47.04/6.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f47,plain,(
% 47.04/6.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.04/6.49    inference(nnf_transformation,[],[f3])).
% 47.04/6.49  
% 47.04/6.49  fof(f48,plain,(
% 47.04/6.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.04/6.49    inference(flattening,[],[f47])).
% 47.04/6.49  
% 47.04/6.49  fof(f56,plain,(
% 47.04/6.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f48])).
% 47.04/6.49  
% 47.04/6.49  fof(f57,plain,(
% 47.04/6.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 47.04/6.49    inference(cnf_transformation,[],[f48])).
% 47.04/6.49  
% 47.04/6.49  fof(f91,plain,(
% 47.04/6.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 47.04/6.49    inference(equality_resolution,[],[f57])).
% 47.04/6.49  
% 47.04/6.49  fof(f58,plain,(
% 47.04/6.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 47.04/6.49    inference(cnf_transformation,[],[f48])).
% 47.04/6.49  
% 47.04/6.49  fof(f90,plain,(
% 47.04/6.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 47.04/6.49    inference(equality_resolution,[],[f58])).
% 47.04/6.49  
% 47.04/6.49  fof(f80,plain,(
% 47.04/6.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(cnf_transformation,[],[f51])).
% 47.04/6.49  
% 47.04/6.49  fof(f92,plain,(
% 47.04/6.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.04/6.49    inference(equality_resolution,[],[f80])).
% 47.04/6.49  
% 47.04/6.49  fof(f93,plain,(
% 47.04/6.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 47.04/6.49    inference(equality_resolution,[],[f92])).
% 47.04/6.49  
% 47.04/6.49  fof(f2,axiom,(
% 47.04/6.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f24,plain,(
% 47.04/6.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 47.04/6.49    inference(ennf_transformation,[],[f2])).
% 47.04/6.49  
% 47.04/6.49  fof(f55,plain,(
% 47.04/6.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f24])).
% 47.04/6.49  
% 47.04/6.49  fof(f63,plain,(
% 47.04/6.49    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f50])).
% 47.04/6.49  
% 47.04/6.49  fof(f10,axiom,(
% 47.04/6.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 47.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.04/6.49  
% 47.04/6.49  fof(f30,plain,(
% 47.04/6.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 47.04/6.49    inference(ennf_transformation,[],[f10])).
% 47.04/6.49  
% 47.04/6.49  fof(f31,plain,(
% 47.04/6.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 47.04/6.49    inference(flattening,[],[f30])).
% 47.04/6.49  
% 47.04/6.49  fof(f69,plain,(
% 47.04/6.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 47.04/6.49    inference(cnf_transformation,[],[f31])).
% 47.04/6.49  
% 47.04/6.49  cnf(c_33,negated_conjecture,
% 47.04/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 47.04/6.49      inference(cnf_transformation,[],[f86]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1541,plain,
% 47.04/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_28,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | ~ v1_funct_1(X0)
% 47.04/6.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 47.04/6.49      inference(cnf_transformation,[],[f81]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1544,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.04/6.49      | v1_funct_1(X0) != iProver_top
% 47.04/6.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2669,plain,
% 47.04/6.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 47.04/6.49      | v1_funct_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1541,c_1544]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_29,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | ~ v1_funct_1(X0)
% 47.04/6.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 47.04/6.49      inference(cnf_transformation,[],[f83]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1543,plain,
% 47.04/6.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 47.04/6.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.04/6.49      | v1_funct_1(X2) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2254,plain,
% 47.04/6.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 47.04/6.49      | v1_funct_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1541,c_1543]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_35,negated_conjecture,
% 47.04/6.49      ( v1_funct_1(sK3) ),
% 47.04/6.49      inference(cnf_transformation,[],[f84]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_36,plain,
% 47.04/6.49      ( v1_funct_1(sK3) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2498,plain,
% 47.04/6.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_2254,c_36]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2672,plain,
% 47.04/6.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 47.04/6.49      | v1_funct_1(sK3) != iProver_top ),
% 47.04/6.49      inference(light_normalisation,[status(thm)],[c_2669,c_2498]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2951,plain,
% 47.04/6.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_2672,c_36]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.04/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1560,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,X1) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_18,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 47.04/6.49      inference(cnf_transformation,[],[f72]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1548,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) = iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2403,plain,
% 47.04/6.49      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1541,c_1548]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_12,plain,
% 47.04/6.49      ( ~ v4_relat_1(X0,X1)
% 47.04/6.49      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 47.04/6.49      | ~ v1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f66]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1554,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) != iProver_top
% 47.04/6.49      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4011,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 47.04/6.49      | v1_relat_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2403,c_1554]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_14,plain,
% 47.04/6.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 47.04/6.49      inference(cnf_transformation,[],[f68]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1552,plain,
% 47.04/6.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.04/6.49      inference(cnf_transformation,[],[f59]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1559,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2328,plain,
% 47.04/6.49      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1541,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f61]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_253,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.04/6.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_254,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_253]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_316,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 47.04/6.49      inference(bin_hyper_res,[status(thm)],[c_7,c_254]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1539,plain,
% 47.04/6.49      ( r1_tarski(X0,X1) != iProver_top
% 47.04/6.49      | v1_relat_1(X1) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2495,plain,
% 47.04/6.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 47.04/6.49      | v1_relat_1(sK3) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2328,c_1539]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2559,plain,
% 47.04/6.49      ( v1_relat_1(sK3) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1552,c_2495]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4307,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_4011,c_2559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_9,plain,
% 47.04/6.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f62]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1557,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_0,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 47.04/6.49      inference(cnf_transformation,[],[f54]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1562,plain,
% 47.04/6.49      ( r1_tarski(X0,X1) != iProver_top
% 47.04/6.49      | r1_tarski(X2,X0) != iProver_top
% 47.04/6.49      | r1_tarski(X2,X1) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3376,plain,
% 47.04/6.49      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2328,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_20,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 47.04/6.49      inference(cnf_transformation,[],[f74]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1546,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3880,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k2_zfmisc_1(X3,X2)) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1560,c_1546]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15555,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 47.04/6.49      | r1_tarski(X0,sK3) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3376,c_3880]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_19,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f73]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1547,plain,
% 47.04/6.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.04/6.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_17347,plain,
% 47.04/6.49      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 47.04/6.49      | r1_tarski(X1,sK3) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_15555,c_1547]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_33893,plain,
% 47.04/6.49      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 47.04/6.49      | v4_relat_1(X1,X0) != iProver_top
% 47.04/6.49      | r1_tarski(X1,sK3) != iProver_top
% 47.04/6.49      | v1_relat_1(X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1557,c_17347]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_95249,plain,
% 47.04/6.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_4307,c_33893]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2587,plain,
% 47.04/6.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_14]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2588,plain,
% 47.04/6.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_16,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f70]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4484,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_16]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4485,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 47.04/6.49      | v1_relat_1(sK3) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_4484]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_27,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | ~ v1_funct_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f82]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1545,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.04/6.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 47.04/6.49      | v1_funct_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3168,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 47.04/6.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2498,c_1545]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_38,plain,
% 47.04/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3820,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_3168,c_36,c_38]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3827,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3820,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5385,plain,
% 47.04/6.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 47.04/6.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3827,c_1539]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_95985,plain,
% 47.04/6.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_95249,c_2559,c_2588,c_4485,c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_24,plain,
% 47.04/6.49      ( v1_funct_2(X0,X1,X2)
% 47.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | k1_relset_1(X1,X2,X0) != X1
% 47.04/6.49      | k1_xboole_0 = X2 ),
% 47.04/6.49      inference(cnf_transformation,[],[f77]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_30,negated_conjecture,
% 47.04/6.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 47.04/6.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 47.04/6.49      inference(cnf_transformation,[],[f89]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_513,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 47.04/6.49      | k1_relset_1(X1,X2,X0) != X1
% 47.04/6.49      | sK2 != X1
% 47.04/6.49      | sK1 != X2
% 47.04/6.49      | k1_xboole_0 = X2 ),
% 47.04/6.49      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_514,plain,
% 47.04/6.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 47.04/6.49      | k1_xboole_0 = sK1 ),
% 47.04/6.49      inference(unflattening,[status(thm)],[c_513]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1534,plain,
% 47.04/6.49      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 47.04/6.49      | k1_xboole_0 = sK1
% 47.04/6.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2504,plain,
% 47.04/6.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 47.04/6.49      | sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_2498,c_1534]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_95988,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 47.04/6.49      | sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_95985,c_2504]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_32,negated_conjecture,
% 47.04/6.49      ( r1_tarski(sK2,sK0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f87]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1542,plain,
% 47.04/6.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_26,plain,
% 47.04/6.49      ( ~ v1_funct_2(X0,X1,X2)
% 47.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | k1_relset_1(X1,X2,X0) = X1
% 47.04/6.49      | k1_xboole_0 = X2 ),
% 47.04/6.49      inference(cnf_transformation,[],[f75]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_34,negated_conjecture,
% 47.04/6.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 47.04/6.49      inference(cnf_transformation,[],[f85]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_529,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.04/6.49      | k1_relset_1(X1,X2,X0) = X1
% 47.04/6.49      | sK3 != X0
% 47.04/6.49      | sK1 != X2
% 47.04/6.49      | sK0 != X1
% 47.04/6.49      | k1_xboole_0 = X2 ),
% 47.04/6.49      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_530,plain,
% 47.04/6.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 47.04/6.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 47.04/6.49      | k1_xboole_0 = sK1 ),
% 47.04/6.49      inference(unflattening,[status(thm)],[c_529]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_532,plain,
% 47.04/6.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_530,c_33]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2757,plain,
% 47.04/6.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1541,c_1547]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2923,plain,
% 47.04/6.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_532,c_2757]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_17,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 47.04/6.49      | ~ v1_relat_1(X1)
% 47.04/6.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f71]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1549,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 47.04/6.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4000,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 47.04/6.49      | sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(X0,sK0) != iProver_top
% 47.04/6.49      | v1_relat_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2923,c_1549]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5146,plain,
% 47.04/6.49      ( r1_tarski(X0,sK0) != iProver_top
% 47.04/6.49      | sK1 = k1_xboole_0
% 47.04/6.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_4000,c_2559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5147,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 47.04/6.49      | sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(X0,sK0) != iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_5146]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5154,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1542,c_5147]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107329,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_95988,c_5154]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_31,negated_conjecture,
% 47.04/6.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f88]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_98,plain,
% 47.04/6.49      ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
% 47.04/6.49      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 47.04/6.49      | ~ v1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_9]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_108,plain,
% 47.04/6.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_5]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4,plain,
% 47.04/6.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 = X0
% 47.04/6.49      | k1_xboole_0 = X1 ),
% 47.04/6.49      inference(cnf_transformation,[],[f56]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_110,plain,
% 47.04/6.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 = k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_4]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3,plain,
% 47.04/6.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f91]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_111,plain,
% 47.04/6.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_3]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_862,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1609,plain,
% 47.04/6.49      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_862]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1610,plain,
% 47.04/6.49      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1609]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1607,plain,
% 47.04/6.49      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_862]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1615,plain,
% 47.04/6.49      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1607]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_861,plain,( X0 = X0 ),theory(equality) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1628,plain,
% 47.04/6.49      ( sK0 = sK0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_861]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1649,plain,
% 47.04/6.49      ( sK2 = sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_861]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1685,plain,
% 47.04/6.49      ( ~ v4_relat_1(k1_xboole_0,sK2)
% 47.04/6.49      | r1_tarski(k1_relat_1(k1_xboole_0),sK2)
% 47.04/6.49      | ~ v1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_9]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_866,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.04/6.49      theory(equality) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1640,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,X1)
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 47.04/6.49      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
% 47.04/6.49      | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_866]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1697,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 47.04/6.49      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X1)
% 47.04/6.49      | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1640]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1699,plain,
% 47.04/6.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | k1_xboole_0 != k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1697]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_865,plain,
% 47.04/6.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 47.04/6.49      theory(equality) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1851,plain,
% 47.04/6.49      ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
% 47.04/6.49      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(X0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_865]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1852,plain,
% 47.04/6.49      ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
% 47.04/6.49      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1851]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2,plain,
% 47.04/6.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f90]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1935,plain,
% 47.04/6.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2,c_1552]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1937,plain,
% 47.04/6.49      ( v1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_1935]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2064,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,sK2)
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_18]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2066,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,sK2)
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2064]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2107,plain,
% 47.04/6.49      ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2200,plain,
% 47.04/6.49      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_861]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2409,plain,
% 47.04/6.49      ( v4_relat_1(sK3,sK0) ),
% 47.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_2403]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2451,plain,
% 47.04/6.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_862]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2452,plain,
% 47.04/6.49      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2451]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_540,plain,
% 47.04/6.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 47.04/6.49      | sK2 != sK0
% 47.04/6.49      | sK1 != sK1 ),
% 47.04/6.49      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_623,plain,
% 47.04/6.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 47.04/6.49      | sK2 != sK0 ),
% 47.04/6.49      inference(equality_resolution_simp,[status(thm)],[c_540]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1533,plain,
% 47.04/6.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 47.04/6.49      | sK2 != sK0
% 47.04/6.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2503,plain,
% 47.04/6.49      ( k7_relat_1(sK3,sK2) != sK3
% 47.04/6.49      | sK2 != sK0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_2498,c_1533]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2560,plain,
% 47.04/6.49      ( v1_relat_1(sK3) ),
% 47.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_2559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2597,plain,
% 47.04/6.49      ( ~ v4_relat_1(sK3,sK0)
% 47.04/6.49      | r1_tarski(k1_relat_1(sK3),sK0)
% 47.04/6.49      | ~ v1_relat_1(sK3) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_9]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_21,plain,
% 47.04/6.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 47.04/6.49      | k1_xboole_0 = X0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f93]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_435,plain,
% 47.04/6.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 47.04/6.49      | sK2 != X0
% 47.04/6.49      | sK1 != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 = X0 ),
% 47.04/6.49      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_436,plain,
% 47.04/6.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 47.04/6.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 47.04/6.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 47.04/6.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 47.04/6.49      | sK1 != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 = sK2 ),
% 47.04/6.49      inference(unflattening,[status(thm)],[c_435]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1538,plain,
% 47.04/6.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 47.04/6.49      | sK1 != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 = sK2
% 47.04/6.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 47.04/6.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1565,plain,
% 47.04/6.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 47.04/6.49      | sK2 = k1_xboole_0
% 47.04/6.49      | sK1 != k1_xboole_0
% 47.04/6.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_1538,c_2]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2502,plain,
% 47.04/6.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 47.04/6.49      | sK2 = k1_xboole_0
% 47.04/6.49      | sK1 != k1_xboole_0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_2498,c_1565]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1606,plain,
% 47.04/6.49      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_862]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1613,plain,
% 47.04/6.49      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1606]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f55]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1622,plain,
% 47.04/6.49      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_863,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.04/6.49      theory(equality) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1657,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1)
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0)
% 47.04/6.49      | sK2 != X0
% 47.04/6.49      | k1_xboole_0 != X1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_863]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1915,plain,
% 47.04/6.49      ( ~ r1_tarski(sK2,X0)
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0)
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1657]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2359,plain,
% 47.04/6.49      ( ~ r1_tarski(sK2,sK0)
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0)
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | k1_xboole_0 != sK0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1915]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2602,plain,
% 47.04/6.49      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_2502,c_32,c_31,c_110,c_111,c_1613,c_1622,c_1649,c_2359,
% 47.04/6.49                 c_2452]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2603,plain,
% 47.04/6.49      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_2602]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2404,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) = iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2,c_1548]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2751,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1560,c_2404]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2752,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) | ~ r1_tarski(X0,k1_xboole_0) ),
% 47.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_2751]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2754,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,k1_xboole_0)
% 47.04/6.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2752]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1550,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1561,plain,
% 47.04/6.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2249,plain,
% 47.04/6.49      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 47.04/6.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1550,c_1561]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3022,plain,
% 47.04/6.49      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_2249,c_1935]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3025,plain,
% 47.04/6.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 47.04/6.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3022,c_1550]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3027,plain,
% 47.04/6.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) | ~ v1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3025]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1815,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK2) | X2 != X0 | sK2 != X1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_863]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2312,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,sK2) | r1_tarski(X1,sK2) | X1 != X0 | sK2 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1815]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3126,plain,
% 47.04/6.49      ( r1_tarski(X0,sK2)
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(X1),sK2)
% 47.04/6.49      | X0 != k1_relat_1(X1)
% 47.04/6.49      | sK2 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2312]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3128,plain,
% 47.04/6.49      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2)
% 47.04/6.49      | r1_tarski(k1_xboole_0,sK2)
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_3126]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3237,plain,
% 47.04/6.49      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
% 47.04/6.49      | k1_xboole_0 = k1_relat_1(X0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3239,plain,
% 47.04/6.49      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 47.04/6.49      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_3237]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1762,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1)
% 47.04/6.49      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 47.04/6.49      | k1_relat_1(sK3) != X0
% 47.04/6.49      | k1_xboole_0 != X1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_863]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1983,plain,
% 47.04/6.49      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 47.04/6.49      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 47.04/6.49      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 47.04/6.49      | k1_xboole_0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1762]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3969,plain,
% 47.04/6.49      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 47.04/6.49      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 47.04/6.49      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 47.04/6.49      | k1_xboole_0 != sK0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1983]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 47.04/6.49      inference(cnf_transformation,[],[f63]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2767,plain,
% 47.04/6.49      ( v4_relat_1(X0,sK2)
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(X0),sK2)
% 47.04/6.49      | ~ v1_relat_1(X0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_8]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5283,plain,
% 47.04/6.49      ( v4_relat_1(sK3,sK2)
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(sK3),sK2)
% 47.04/6.49      | ~ v1_relat_1(sK3) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2767]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1799,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK2) | r1_tarski(X0,sK2) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_0]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6177,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,sK2)
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 47.04/6.49      | r1_tarski(k1_relat_1(sK3),sK2) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1799]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6184,plain,
% 47.04/6.49      ( r1_tarski(k1_relat_1(sK3),sK2)
% 47.04/6.49      | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 47.04/6.49      | ~ r1_tarski(k1_xboole_0,sK2) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_6177]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15,plain,
% 47.04/6.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 47.04/6.49      inference(cnf_transformation,[],[f69]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_49317,plain,
% 47.04/6.49      ( ~ v4_relat_1(sK3,sK2) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,sK2) = sK3 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_15]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107333,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_107329,c_31,c_98,c_108,c_110,c_111,c_1610,c_1615,c_1628,
% 47.04/6.49                 c_1649,c_1685,c_1699,c_1852,c_1937,c_2066,c_2107,c_2200,
% 47.04/6.49                 c_2409,c_2452,c_2503,c_2560,c_2597,c_2603,c_2754,c_3027,
% 47.04/6.49                 c_3128,c_3239,c_3969,c_5283,c_6184,c_49317]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107337,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1560,c_107333]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,X1) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_109,plain,
% 47.04/6.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_107]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_875,plain,
% 47.04/6.49      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | k1_xboole_0 != k1_xboole_0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_865]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2356,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,X1)
% 47.04/6.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | X2 != X0
% 47.04/6.49      | k1_zfmisc_1(k1_xboole_0) != X1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_866]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3401,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | X1 != X0
% 47.04/6.49      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2356]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_11260,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | sK2 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_3401]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_11261,plain,
% 47.04/6.49      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | sK2 != X0
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_11260]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_11263,plain,
% 47.04/6.49      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | sK2 != k1_xboole_0
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_11261]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_37752,plain,
% 47.04/6.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_5385,c_2588]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5483,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
% 47.04/6.49      | r1_tarski(sK2,X0) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_5154,c_1557]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5616,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(sK2,sK2) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_4307,c_5483]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1686,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,sK2) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
% 47.04/6.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1698,plain,
% 47.04/6.49      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X0)
% 47.04/6.49      | k1_xboole_0 != X1
% 47.04/6.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1700,plain,
% 47.04/6.49      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 47.04/6.49      | k1_xboole_0 != k1_xboole_0
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_1698]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2065,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,sK2) = iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2064]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2067,plain,
% 47.04/6.49      ( v4_relat_1(k1_xboole_0,sK2) = iProver_top
% 47.04/6.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2065]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3127,plain,
% 47.04/6.49      ( X0 != k1_relat_1(X1)
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | r1_tarski(X0,sK2) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X1),sK2) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_3126]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3129,plain,
% 47.04/6.49      ( sK2 != sK2
% 47.04/6.49      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 47.04/6.49      | r1_tarski(k1_relat_1(k1_xboole_0),sK2) != iProver_top
% 47.04/6.49      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_3127]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6650,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,sK2) | r1_tarski(sK2,sK2) | sK2 != X0 | sK2 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_2312]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6653,plain,
% 47.04/6.49      ( sK2 != X0
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | r1_tarski(X0,sK2) != iProver_top
% 47.04/6.49      | r1_tarski(sK2,sK2) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_6650]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_6655,plain,
% 47.04/6.49      ( sK2 != sK2
% 47.04/6.49      | sK2 != k1_xboole_0
% 47.04/6.49      | r1_tarski(sK2,sK2) = iProver_top
% 47.04/6.49      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_6653]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_41670,plain,
% 47.04/6.49      ( r1_tarski(sK2,sK2) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_5616,c_98,c_109,c_110,c_111,c_1649,c_1686,c_1700,c_1852,
% 47.04/6.49                 c_1935,c_1937,c_2067,c_2107,c_2603,c_2754,c_3025,c_3027,
% 47.04/6.49                 c_3129,c_3239,c_6655]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_41675,plain,
% 47.04/6.49      ( r1_tarski(sK2,sK2) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_37752,c_41670]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_47420,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1)
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 47.04/6.49      | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
% 47.04/6.49      | sK2 != X1 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_863]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_53693,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,sK2)
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 47.04/6.49      | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
% 47.04/6.49      | sK2 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_47420]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_60560,plain,
% 47.04/6.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 47.04/6.49      | ~ r1_tarski(sK2,sK2)
% 47.04/6.49      | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 47.04/6.49      | sK2 != sK2 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_53693]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_60561,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 47.04/6.49      | sK2 != sK2
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 47.04/6.49      | r1_tarski(sK2,sK2) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_60560]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1551,plain,
% 47.04/6.49      ( k7_relat_1(X0,X1) = X0
% 47.04/6.49      | v4_relat_1(X0,X1) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4315,plain,
% 47.04/6.49      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_4307,c_1551]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7049,plain,
% 47.04/6.49      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_4315,c_2588,c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7053,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,X0)) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_7049,c_1550]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_12237,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,X0)) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_7053,c_2588,c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3885,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3,c_1546]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5267,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3885,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1889,plain,
% 47.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1890,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15564,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3,c_3880]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_97,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2353,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | ~ r1_tarski(X0,k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_5]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_2354,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3617,plain,
% 47.04/6.49      ( r1_tarski(X0,sK3) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) = iProver_top
% 47.04/6.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3376,c_1539]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7524,plain,
% 47.04/6.49      ( v1_relat_1(X0) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_3617,c_2588]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7525,plain,
% 47.04/6.49      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_7524]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3275,plain,
% 47.04/6.49      ( k1_relat_1(X0) = k1_xboole_0
% 47.04/6.49      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1557,c_1561]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7236,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_4307,c_3275]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_5391,plain,
% 47.04/6.49      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 47.04/6.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_7430,plain,
% 47.04/6.49      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_7236,c_2588,c_5391]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_3883,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3820,c_1546]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8029,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3,c_3883]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8291,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_7430,c_8029]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4015,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 47.04/6.49      | v1_relat_1(sK3) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_4011]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8290,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1557,c_8029]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8296,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_8290]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_9138,plain,
% 47.04/6.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_8291,c_2559,c_2588,c_4015,c_5391,c_8296]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_9142,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_9138,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_9327,plain,
% 47.04/6.49      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_9142,c_1561]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_9338,plain,
% 47.04/6.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 47.04/6.49      | v1_relat_1(sK3) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_9327,c_1550]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_10424,plain,
% 47.04/6.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,[status(thm)],[c_9338,c_2559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_10429,plain,
% 47.04/6.49      ( r1_tarski(X0,sK3) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_10424,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15590,plain,
% 47.04/6.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_15564,c_97,c_2354,c_2751,c_3885,c_7525,c_10429]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15591,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_15590]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15598,plain,
% 47.04/6.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_15591,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_34244,plain,
% 47.04/6.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 47.04/6.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_5267,c_1890,c_15598]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_34245,plain,
% 47.04/6.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_34244]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1558,plain,
% 47.04/6.49      ( v4_relat_1(X0,X1) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_34257,plain,
% 47.04/6.49      ( v4_relat_1(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 47.04/6.49      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_34245,c_1558]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_36331,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_5154,c_34257]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1654,plain,
% 47.04/6.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_1655,plain,
% 47.04/6.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8292,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_5154,c_8029]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8540,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_8292,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_13165,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 47.04/6.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_8540,c_1539]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_36564,plain,
% 47.04/6.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
% 47.04/6.49      | sK1 = k1_xboole_0 ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_36331,c_1655,c_1935,c_13165]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_36565,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) = iProver_top
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_36564]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_36570,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2,c_36565]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_8030,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(X1,sK1)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3883,c_1559]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_14814,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3,c_8030]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_14834,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1557,c_14814]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_46164,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_14834,c_2588,c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_46165,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_46164]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_46172,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_36570,c_46165]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_46190,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_46172,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4266,plain,
% 47.04/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,X2) | X2 != X1 | sK0 != X0 ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_863]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4267,plain,
% 47.04/6.49      ( X0 != X1
% 47.04/6.49      | sK0 != X2
% 47.04/6.49      | r1_tarski(X2,X1) != iProver_top
% 47.04/6.49      | r1_tarski(sK0,X0) = iProver_top ),
% 47.04/6.49      inference(predicate_to_equality,[status(thm)],[c_4266]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_4269,plain,
% 47.04/6.49      ( sK0 != k1_xboole_0
% 47.04/6.49      | k1_xboole_0 != k1_xboole_0
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(instantiation,[status(thm)],[c_4267]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_13164,plain,
% 47.04/6.49      ( sK1 = k1_xboole_0
% 47.04/6.49      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_8540,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_15772,plain,
% 47.04/6.49      ( r1_tarski(X0,X1) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top
% 47.04/6.49      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_15598,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_21946,plain,
% 47.04/6.49      ( r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1542,c_15772]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_22040,plain,
% 47.04/6.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 47.04/6.49      | r1_tarski(X0,sK2) != iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_21946,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_22570,plain,
% 47.04/6.49      ( r1_tarski(X0,sK2) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2,c_22040]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_22941,plain,
% 47.04/6.49      ( v4_relat_1(X0,sK2) != iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_1557,c_22570]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_14816,plain,
% 47.04/6.49      ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k2_zfmisc_1(X2,sK1)) = iProver_top
% 47.04/6.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X2) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_8030,c_1562]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_65586,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_22941,c_14816]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_65796,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 47.04/6.49      inference(demodulation,[status(thm)],[c_65586,c_3]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_66326,plain,
% 47.04/6.49      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
% 47.04/6.49      | v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_65796,c_2588,c_5385]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_66327,plain,
% 47.04/6.49      ( v4_relat_1(k7_relat_1(sK3,X0),sK2) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k7_relat_1(sK3,X0)) != iProver_top
% 47.04/6.49      | r1_tarski(X1,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(renaming,[status(thm)],[c_66326]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_66331,plain,
% 47.04/6.49      ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 47.04/6.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_4307,c_66327]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_71242,plain,
% 47.04/6.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 47.04/6.49      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_46190,c_31,c_110,c_111,c_1615,c_1628,c_1655,c_1935,c_2452,
% 47.04/6.49                 c_3025,c_4269,c_13164,c_66331]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_71252,plain,
% 47.04/6.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.04/6.49      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_12237,c_71242]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107339,plain,
% 47.04/6.49      ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_15591,c_107333]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107341,plain,
% 47.04/6.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 47.04/6.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_3883,c_107333]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107770,plain,
% 47.04/6.49      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 47.04/6.49      inference(global_propositional_subsumption,
% 47.04/6.49                [status(thm)],
% 47.04/6.49                [c_107337,c_109,c_110,c_111,c_875,c_1649,c_1935,c_2603,
% 47.04/6.49                 c_3025,c_5154,c_11263,c_41675,c_60561,c_71252,c_107339,
% 47.04/6.49                 c_107341]) ).
% 47.04/6.49  
% 47.04/6.49  cnf(c_107774,plain,
% 47.04/6.49      ( $false ),
% 47.04/6.49      inference(superposition,[status(thm)],[c_2951,c_107770]) ).
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.04/6.49  
% 47.04/6.49  ------                               Statistics
% 47.04/6.49  
% 47.04/6.49  ------ General
% 47.04/6.49  
% 47.04/6.49  abstr_ref_over_cycles:                  0
% 47.04/6.49  abstr_ref_under_cycles:                 0
% 47.04/6.49  gc_basic_clause_elim:                   0
% 47.04/6.49  forced_gc_time:                         0
% 47.04/6.49  parsing_time:                           0.01
% 47.04/6.49  unif_index_cands_time:                  0.
% 47.04/6.49  unif_index_add_time:                    0.
% 47.04/6.49  orderings_time:                         0.
% 47.04/6.49  out_proof_time:                         0.055
% 47.04/6.49  total_time:                             5.579
% 47.04/6.49  num_of_symbols:                         48
% 47.04/6.49  num_of_terms:                           80261
% 47.04/6.49  
% 47.04/6.49  ------ Preprocessing
% 47.04/6.49  
% 47.04/6.49  num_of_splits:                          0
% 47.04/6.49  num_of_split_atoms:                     0
% 47.04/6.49  num_of_reused_defs:                     0
% 47.04/6.49  num_eq_ax_congr_red:                    11
% 47.04/6.49  num_of_sem_filtered_clauses:            1
% 47.04/6.49  num_of_subtypes:                        0
% 47.04/6.49  monotx_restored_types:                  0
% 47.04/6.49  sat_num_of_epr_types:                   0
% 47.04/6.49  sat_num_of_non_cyclic_types:            0
% 47.04/6.49  sat_guarded_non_collapsed_types:        0
% 47.04/6.49  num_pure_diseq_elim:                    0
% 47.04/6.49  simp_replaced_by:                       0
% 47.04/6.49  res_preprocessed:                       166
% 47.04/6.49  prep_upred:                             0
% 47.04/6.49  prep_unflattend:                        33
% 47.04/6.49  smt_new_axioms:                         0
% 47.04/6.49  pred_elim_cands:                        5
% 47.04/6.49  pred_elim:                              1
% 47.04/6.49  pred_elim_cl:                           1
% 47.04/6.49  pred_elim_cycles:                       3
% 47.04/6.49  merged_defs:                            8
% 47.04/6.49  merged_defs_ncl:                        0
% 47.04/6.49  bin_hyper_res:                          9
% 47.04/6.49  prep_cycles:                            4
% 47.04/6.49  pred_elim_time:                         0.006
% 47.04/6.49  splitting_time:                         0.
% 47.04/6.49  sem_filter_time:                        0.
% 47.04/6.49  monotx_time:                            0.
% 47.04/6.49  subtype_inf_time:                       0.
% 47.04/6.49  
% 47.04/6.49  ------ Problem properties
% 47.04/6.49  
% 47.04/6.49  clauses:                                35
% 47.04/6.49  conjectures:                            4
% 47.04/6.49  epr:                                    6
% 47.04/6.49  horn:                                   32
% 47.04/6.49  ground:                                 11
% 47.04/6.49  unary:                                  6
% 47.04/6.49  binary:                                 9
% 47.04/6.49  lits:                                   92
% 47.04/6.49  lits_eq:                                28
% 47.04/6.49  fd_pure:                                0
% 47.04/6.49  fd_pseudo:                              0
% 47.04/6.49  fd_cond:                                2
% 47.04/6.49  fd_pseudo_cond:                         0
% 47.04/6.49  ac_symbols:                             0
% 47.04/6.49  
% 47.04/6.49  ------ Propositional Solver
% 47.04/6.49  
% 47.04/6.49  prop_solver_calls:                      58
% 47.04/6.49  prop_fast_solver_calls:                 7685
% 47.04/6.49  smt_solver_calls:                       0
% 47.04/6.49  smt_fast_solver_calls:                  0
% 47.04/6.49  prop_num_of_clauses:                    57113
% 47.04/6.49  prop_preprocess_simplified:             80527
% 47.04/6.49  prop_fo_subsumed:                       792
% 47.04/6.49  prop_solver_time:                       0.
% 47.04/6.49  smt_solver_time:                        0.
% 47.04/6.49  smt_fast_solver_time:                   0.
% 47.04/6.49  prop_fast_solver_time:                  0.
% 47.04/6.49  prop_unsat_core_time:                   0.
% 47.04/6.49  
% 47.04/6.49  ------ QBF
% 47.04/6.49  
% 47.04/6.49  qbf_q_res:                              0
% 47.04/6.49  qbf_num_tautologies:                    0
% 47.04/6.49  qbf_prep_cycles:                        0
% 47.04/6.49  
% 47.04/6.49  ------ BMC1
% 47.04/6.49  
% 47.04/6.49  bmc1_current_bound:                     -1
% 47.04/6.49  bmc1_last_solved_bound:                 -1
% 47.04/6.49  bmc1_unsat_core_size:                   -1
% 47.04/6.49  bmc1_unsat_core_parents_size:           -1
% 47.04/6.49  bmc1_merge_next_fun:                    0
% 47.04/6.49  bmc1_unsat_core_clauses_time:           0.
% 47.04/6.49  
% 47.04/6.49  ------ Instantiation
% 47.04/6.49  
% 47.04/6.49  inst_num_of_clauses:                    12168
% 47.04/6.49  inst_num_in_passive:                    6966
% 47.04/6.49  inst_num_in_active:                     7210
% 47.04/6.49  inst_num_in_unprocessed:                834
% 47.04/6.49  inst_num_of_loops:                      7409
% 47.04/6.49  inst_num_of_learning_restarts:          1
% 47.04/6.49  inst_num_moves_active_passive:          188
% 47.04/6.49  inst_lit_activity:                      0
% 47.04/6.49  inst_lit_activity_moves:                0
% 47.04/6.49  inst_num_tautologies:                   0
% 47.04/6.49  inst_num_prop_implied:                  0
% 47.04/6.49  inst_num_existing_simplified:           0
% 47.04/6.49  inst_num_eq_res_simplified:             0
% 47.04/6.49  inst_num_child_elim:                    0
% 47.04/6.49  inst_num_of_dismatching_blockings:      9782
% 47.04/6.49  inst_num_of_non_proper_insts:           14655
% 47.04/6.49  inst_num_of_duplicates:                 0
% 47.04/6.49  inst_inst_num_from_inst_to_res:         0
% 47.04/6.49  inst_dismatching_checking_time:         0.
% 47.04/6.49  
% 47.04/6.49  ------ Resolution
% 47.04/6.49  
% 47.04/6.49  res_num_of_clauses:                     47
% 47.04/6.49  res_num_in_passive:                     47
% 47.04/6.49  res_num_in_active:                      0
% 47.04/6.49  res_num_of_loops:                       170
% 47.04/6.49  res_forward_subset_subsumed:            306
% 47.04/6.49  res_backward_subset_subsumed:           0
% 47.04/6.49  res_forward_subsumed:                   0
% 47.04/6.49  res_backward_subsumed:                  0
% 47.04/6.49  res_forward_subsumption_resolution:     0
% 47.04/6.49  res_backward_subsumption_resolution:    0
% 47.04/6.49  res_clause_to_clause_subsumption:       70498
% 47.04/6.49  res_orphan_elimination:                 0
% 47.04/6.49  res_tautology_del:                      954
% 47.04/6.49  res_num_eq_res_simplified:              1
% 47.04/6.49  res_num_sel_changes:                    0
% 47.04/6.49  res_moves_from_active_to_pass:          0
% 47.04/6.49  
% 47.04/6.49  ------ Superposition
% 47.04/6.49  
% 47.04/6.49  sup_time_total:                         0.
% 47.04/6.49  sup_time_generating:                    0.
% 47.04/6.49  sup_time_sim_full:                      0.
% 47.04/6.49  sup_time_sim_immed:                     0.
% 47.04/6.49  
% 47.04/6.49  sup_num_of_clauses:                     8060
% 47.04/6.49  sup_num_in_active:                      1237
% 47.04/6.49  sup_num_in_passive:                     6823
% 47.04/6.49  sup_num_of_loops:                       1480
% 47.04/6.49  sup_fw_superposition:                   9774
% 47.04/6.49  sup_bw_superposition:                   8725
% 47.04/6.49  sup_immediate_simplified:               7567
% 47.04/6.49  sup_given_eliminated:                   22
% 47.04/6.49  comparisons_done:                       0
% 47.04/6.49  comparisons_avoided:                    84
% 47.04/6.49  
% 47.04/6.49  ------ Simplifications
% 47.04/6.49  
% 47.04/6.49  
% 47.04/6.49  sim_fw_subset_subsumed:                 1012
% 47.04/6.49  sim_bw_subset_subsumed:                 357
% 47.04/6.49  sim_fw_subsumed:                        5793
% 47.04/6.49  sim_bw_subsumed:                        680
% 47.04/6.49  sim_fw_subsumption_res:                 0
% 47.04/6.49  sim_bw_subsumption_res:                 0
% 47.04/6.49  sim_tautology_del:                      141
% 47.04/6.49  sim_eq_tautology_del:                   213
% 47.04/6.49  sim_eq_res_simp:                        0
% 47.04/6.49  sim_fw_demodulated:                     677
% 47.04/6.49  sim_bw_demodulated:                     9
% 47.04/6.49  sim_light_normalised:                   427
% 47.04/6.49  sim_joinable_taut:                      0
% 47.04/6.49  sim_joinable_simp:                      0
% 47.04/6.49  sim_ac_normalised:                      0
% 47.04/6.49  sim_smt_subsumption:                    0
% 47.04/6.49  
%------------------------------------------------------------------------------
