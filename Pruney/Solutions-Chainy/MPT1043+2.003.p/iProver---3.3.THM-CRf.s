%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:47 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  168 (1036 expanded)
%              Number of clauses        :   99 ( 382 expanded)
%              Number of leaves         :   18 ( 186 expanded)
%              Depth                    :   24
%              Number of atoms          :  481 (3420 expanded)
%              Number of equality atoms :  185 ( 787 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f51])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1356,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X5 != X3
    | X2 != X4
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_476,c_30,c_28])).

cnf(c_1332,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
    | r2_hidden(X1,k1_funct_2(k1_xboole_0,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1332,c_9])).

cnf(c_5265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k5_partfun1(k1_xboole_0,X1,X0),X2),k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,X1,X0),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1468])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1357,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_46313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,X1,X0),k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5265,c_1357])).

cnf(c_46378,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46313])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1352,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_233])).

cnf(c_1335,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_3193,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1335])).

cnf(c_8584,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_3193])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1346,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_21,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_21])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_434,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_22])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_1334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_2118,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_1334])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1344,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1746,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_1344])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1353,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3354,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1353])).

cnf(c_4241,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2118,c_3354])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1337,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_29,c_27])).

cnf(c_455,plain,
    ( r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_30,c_28])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_455])).

cnf(c_1333,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2288,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1333])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2740,plain,
    ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2288,c_34])).

cnf(c_2741,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2740])).

cnf(c_2749,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_2741])).

cnf(c_2757,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_1357])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2932,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_36])).

cnf(c_1747,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1344])).

cnf(c_2937,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2932,c_1747])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2946,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2937,c_8])).

cnf(c_3357,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2946,c_1353])).

cnf(c_3545,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3357,c_1746])).

cnf(c_2120,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1334])).

cnf(c_3356,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2120,c_1353])).

cnf(c_3547,plain,
    ( k1_relat_1(k1_xboole_0) = sK1
    | r1_tarski(sK1,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3545,c_3356])).

cnf(c_4432,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4241,c_3547])).

cnf(c_8782,plain,
    ( sK1 = k1_xboole_0
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8584,c_4432])).

cnf(c_74,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_76,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_87,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_743,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1571,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1572,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_1574,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_735,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1680,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_1681,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1341])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_97,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5491,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5214,c_97])).

cnf(c_5492,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5491])).

cnf(c_1338,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2938,plain,
    ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,sK3),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2932,c_1338])).

cnf(c_3552,plain,
    ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3545,c_2938])).

cnf(c_8785,plain,
    ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8584,c_3552])).

cnf(c_8922,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5492,c_8785])).

cnf(c_9072,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8782,c_34,c_76,c_87,c_88,c_1574,c_1681,c_3545,c_8922])).

cnf(c_9077,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9072,c_3552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46378,c_9077,c_3545,c_1681,c_1574,c_88,c_87,c_76,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.42/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.42/1.49  
% 7.42/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.42/1.49  
% 7.42/1.49  ------  iProver source info
% 7.42/1.49  
% 7.42/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.42/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.42/1.49  git: non_committed_changes: false
% 7.42/1.49  git: last_make_outside_of_git: false
% 7.42/1.49  
% 7.42/1.49  ------ 
% 7.42/1.49  
% 7.42/1.49  ------ Input Options
% 7.42/1.49  
% 7.42/1.49  --out_options                           all
% 7.42/1.49  --tptp_safe_out                         true
% 7.42/1.49  --problem_path                          ""
% 7.42/1.49  --include_path                          ""
% 7.42/1.49  --clausifier                            res/vclausify_rel
% 7.42/1.49  --clausifier_options                    --mode clausify
% 7.42/1.49  --stdin                                 false
% 7.42/1.49  --stats_out                             all
% 7.42/1.49  
% 7.42/1.49  ------ General Options
% 7.42/1.49  
% 7.42/1.49  --fof                                   false
% 7.42/1.49  --time_out_real                         305.
% 7.42/1.49  --time_out_virtual                      -1.
% 7.42/1.49  --symbol_type_check                     false
% 7.42/1.49  --clausify_out                          false
% 7.42/1.49  --sig_cnt_out                           false
% 7.42/1.49  --trig_cnt_out                          false
% 7.42/1.49  --trig_cnt_out_tolerance                1.
% 7.42/1.49  --trig_cnt_out_sk_spl                   false
% 7.42/1.49  --abstr_cl_out                          false
% 7.42/1.49  
% 7.42/1.49  ------ Global Options
% 7.42/1.49  
% 7.42/1.49  --schedule                              default
% 7.42/1.49  --add_important_lit                     false
% 7.42/1.49  --prop_solver_per_cl                    1000
% 7.42/1.49  --min_unsat_core                        false
% 7.42/1.49  --soft_assumptions                      false
% 7.42/1.49  --soft_lemma_size                       3
% 7.42/1.49  --prop_impl_unit_size                   0
% 7.42/1.49  --prop_impl_unit                        []
% 7.42/1.49  --share_sel_clauses                     true
% 7.42/1.49  --reset_solvers                         false
% 7.42/1.49  --bc_imp_inh                            [conj_cone]
% 7.42/1.49  --conj_cone_tolerance                   3.
% 7.42/1.49  --extra_neg_conj                        none
% 7.42/1.49  --large_theory_mode                     true
% 7.42/1.49  --prolific_symb_bound                   200
% 7.42/1.49  --lt_threshold                          2000
% 7.42/1.49  --clause_weak_htbl                      true
% 7.42/1.49  --gc_record_bc_elim                     false
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing Options
% 7.42/1.49  
% 7.42/1.49  --preprocessing_flag                    true
% 7.42/1.49  --time_out_prep_mult                    0.1
% 7.42/1.49  --splitting_mode                        input
% 7.42/1.49  --splitting_grd                         true
% 7.42/1.49  --splitting_cvd                         false
% 7.42/1.49  --splitting_cvd_svl                     false
% 7.42/1.49  --splitting_nvd                         32
% 7.42/1.49  --sub_typing                            true
% 7.42/1.49  --prep_gs_sim                           true
% 7.42/1.49  --prep_unflatten                        true
% 7.42/1.49  --prep_res_sim                          true
% 7.42/1.49  --prep_upred                            true
% 7.42/1.49  --prep_sem_filter                       exhaustive
% 7.42/1.49  --prep_sem_filter_out                   false
% 7.42/1.49  --pred_elim                             true
% 7.42/1.49  --res_sim_input                         true
% 7.42/1.49  --eq_ax_congr_red                       true
% 7.42/1.49  --pure_diseq_elim                       true
% 7.42/1.49  --brand_transform                       false
% 7.42/1.49  --non_eq_to_eq                          false
% 7.42/1.49  --prep_def_merge                        true
% 7.42/1.49  --prep_def_merge_prop_impl              false
% 7.42/1.49  --prep_def_merge_mbd                    true
% 7.42/1.49  --prep_def_merge_tr_red                 false
% 7.42/1.49  --prep_def_merge_tr_cl                  false
% 7.42/1.49  --smt_preprocessing                     true
% 7.42/1.49  --smt_ac_axioms                         fast
% 7.42/1.49  --preprocessed_out                      false
% 7.42/1.49  --preprocessed_stats                    false
% 7.42/1.49  
% 7.42/1.49  ------ Abstraction refinement Options
% 7.42/1.49  
% 7.42/1.49  --abstr_ref                             []
% 7.42/1.49  --abstr_ref_prep                        false
% 7.42/1.49  --abstr_ref_until_sat                   false
% 7.42/1.49  --abstr_ref_sig_restrict                funpre
% 7.42/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.49  --abstr_ref_under                       []
% 7.42/1.49  
% 7.42/1.49  ------ SAT Options
% 7.42/1.49  
% 7.42/1.49  --sat_mode                              false
% 7.42/1.49  --sat_fm_restart_options                ""
% 7.42/1.49  --sat_gr_def                            false
% 7.42/1.49  --sat_epr_types                         true
% 7.42/1.49  --sat_non_cyclic_types                  false
% 7.42/1.49  --sat_finite_models                     false
% 7.42/1.49  --sat_fm_lemmas                         false
% 7.42/1.49  --sat_fm_prep                           false
% 7.42/1.49  --sat_fm_uc_incr                        true
% 7.42/1.49  --sat_out_model                         small
% 7.42/1.49  --sat_out_clauses                       false
% 7.42/1.49  
% 7.42/1.49  ------ QBF Options
% 7.42/1.49  
% 7.42/1.49  --qbf_mode                              false
% 7.42/1.49  --qbf_elim_univ                         false
% 7.42/1.49  --qbf_dom_inst                          none
% 7.42/1.49  --qbf_dom_pre_inst                      false
% 7.42/1.49  --qbf_sk_in                             false
% 7.42/1.49  --qbf_pred_elim                         true
% 7.42/1.49  --qbf_split                             512
% 7.42/1.49  
% 7.42/1.49  ------ BMC1 Options
% 7.42/1.49  
% 7.42/1.49  --bmc1_incremental                      false
% 7.42/1.49  --bmc1_axioms                           reachable_all
% 7.42/1.49  --bmc1_min_bound                        0
% 7.42/1.49  --bmc1_max_bound                        -1
% 7.42/1.49  --bmc1_max_bound_default                -1
% 7.42/1.49  --bmc1_symbol_reachability              true
% 7.42/1.49  --bmc1_property_lemmas                  false
% 7.42/1.49  --bmc1_k_induction                      false
% 7.42/1.49  --bmc1_non_equiv_states                 false
% 7.42/1.49  --bmc1_deadlock                         false
% 7.42/1.49  --bmc1_ucm                              false
% 7.42/1.49  --bmc1_add_unsat_core                   none
% 7.42/1.49  --bmc1_unsat_core_children              false
% 7.42/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.49  --bmc1_out_stat                         full
% 7.42/1.49  --bmc1_ground_init                      false
% 7.42/1.49  --bmc1_pre_inst_next_state              false
% 7.42/1.49  --bmc1_pre_inst_state                   false
% 7.42/1.49  --bmc1_pre_inst_reach_state             false
% 7.42/1.49  --bmc1_out_unsat_core                   false
% 7.42/1.49  --bmc1_aig_witness_out                  false
% 7.42/1.49  --bmc1_verbose                          false
% 7.42/1.49  --bmc1_dump_clauses_tptp                false
% 7.42/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.49  --bmc1_dump_file                        -
% 7.42/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.49  --bmc1_ucm_extend_mode                  1
% 7.42/1.49  --bmc1_ucm_init_mode                    2
% 7.42/1.49  --bmc1_ucm_cone_mode                    none
% 7.42/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.49  --bmc1_ucm_relax_model                  4
% 7.42/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.49  --bmc1_ucm_layered_model                none
% 7.42/1.49  --bmc1_ucm_max_lemma_size               10
% 7.42/1.49  
% 7.42/1.49  ------ AIG Options
% 7.42/1.49  
% 7.42/1.49  --aig_mode                              false
% 7.42/1.49  
% 7.42/1.49  ------ Instantiation Options
% 7.42/1.49  
% 7.42/1.49  --instantiation_flag                    true
% 7.42/1.49  --inst_sos_flag                         false
% 7.42/1.49  --inst_sos_phase                        true
% 7.42/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.49  --inst_lit_sel_side                     num_symb
% 7.42/1.49  --inst_solver_per_active                1400
% 7.42/1.49  --inst_solver_calls_frac                1.
% 7.42/1.49  --inst_passive_queue_type               priority_queues
% 7.42/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.49  --inst_passive_queues_freq              [25;2]
% 7.42/1.49  --inst_dismatching                      true
% 7.42/1.49  --inst_eager_unprocessed_to_passive     true
% 7.42/1.49  --inst_prop_sim_given                   true
% 7.42/1.49  --inst_prop_sim_new                     false
% 7.42/1.49  --inst_subs_new                         false
% 7.42/1.49  --inst_eq_res_simp                      false
% 7.42/1.49  --inst_subs_given                       false
% 7.42/1.49  --inst_orphan_elimination               true
% 7.42/1.49  --inst_learning_loop_flag               true
% 7.42/1.49  --inst_learning_start                   3000
% 7.42/1.49  --inst_learning_factor                  2
% 7.42/1.49  --inst_start_prop_sim_after_learn       3
% 7.42/1.49  --inst_sel_renew                        solver
% 7.42/1.49  --inst_lit_activity_flag                true
% 7.42/1.49  --inst_restr_to_given                   false
% 7.42/1.49  --inst_activity_threshold               500
% 7.42/1.49  --inst_out_proof                        true
% 7.42/1.49  
% 7.42/1.49  ------ Resolution Options
% 7.42/1.49  
% 7.42/1.49  --resolution_flag                       true
% 7.42/1.49  --res_lit_sel                           adaptive
% 7.42/1.49  --res_lit_sel_side                      none
% 7.42/1.49  --res_ordering                          kbo
% 7.42/1.49  --res_to_prop_solver                    active
% 7.42/1.49  --res_prop_simpl_new                    false
% 7.42/1.49  --res_prop_simpl_given                  true
% 7.42/1.49  --res_passive_queue_type                priority_queues
% 7.42/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.49  --res_passive_queues_freq               [15;5]
% 7.42/1.49  --res_forward_subs                      full
% 7.42/1.49  --res_backward_subs                     full
% 7.42/1.49  --res_forward_subs_resolution           true
% 7.42/1.49  --res_backward_subs_resolution          true
% 7.42/1.49  --res_orphan_elimination                true
% 7.42/1.49  --res_time_limit                        2.
% 7.42/1.49  --res_out_proof                         true
% 7.42/1.49  
% 7.42/1.49  ------ Superposition Options
% 7.42/1.49  
% 7.42/1.49  --superposition_flag                    true
% 7.42/1.49  --sup_passive_queue_type                priority_queues
% 7.42/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.49  --demod_completeness_check              fast
% 7.42/1.49  --demod_use_ground                      true
% 7.42/1.49  --sup_to_prop_solver                    passive
% 7.42/1.49  --sup_prop_simpl_new                    true
% 7.42/1.49  --sup_prop_simpl_given                  true
% 7.42/1.49  --sup_fun_splitting                     false
% 7.42/1.49  --sup_smt_interval                      50000
% 7.42/1.49  
% 7.42/1.49  ------ Superposition Simplification Setup
% 7.42/1.49  
% 7.42/1.49  --sup_indices_passive                   []
% 7.42/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_full_bw                           [BwDemod]
% 7.42/1.49  --sup_immed_triv                        [TrivRules]
% 7.42/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_immed_bw_main                     []
% 7.42/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.49  
% 7.42/1.49  ------ Combination Options
% 7.42/1.49  
% 7.42/1.49  --comb_res_mult                         3
% 7.42/1.49  --comb_sup_mult                         2
% 7.42/1.49  --comb_inst_mult                        10
% 7.42/1.49  
% 7.42/1.49  ------ Debug Options
% 7.42/1.49  
% 7.42/1.49  --dbg_backtrace                         false
% 7.42/1.49  --dbg_dump_prop_clauses                 false
% 7.42/1.49  --dbg_dump_prop_clauses_file            -
% 7.42/1.49  --dbg_out_stat                          false
% 7.42/1.49  ------ Parsing...
% 7.42/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.42/1.49  ------ Proving...
% 7.42/1.49  ------ Problem Properties 
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  clauses                                 29
% 7.42/1.49  conjectures                             3
% 7.42/1.49  EPR                                     11
% 7.42/1.49  Horn                                    23
% 7.42/1.49  unary                                   8
% 7.42/1.49  binary                                  5
% 7.42/1.49  lits                                    73
% 7.42/1.49  lits eq                                 7
% 7.42/1.49  fd_pure                                 0
% 7.42/1.49  fd_pseudo                               0
% 7.42/1.49  fd_cond                                 2
% 7.42/1.49  fd_pseudo_cond                          1
% 7.42/1.49  AC symbols                              0
% 7.42/1.49  
% 7.42/1.49  ------ Schedule dynamic 5 is on 
% 7.42/1.49  
% 7.42/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  ------ 
% 7.42/1.49  Current options:
% 7.42/1.49  ------ 
% 7.42/1.49  
% 7.42/1.49  ------ Input Options
% 7.42/1.49  
% 7.42/1.49  --out_options                           all
% 7.42/1.49  --tptp_safe_out                         true
% 7.42/1.49  --problem_path                          ""
% 7.42/1.49  --include_path                          ""
% 7.42/1.49  --clausifier                            res/vclausify_rel
% 7.42/1.49  --clausifier_options                    --mode clausify
% 7.42/1.49  --stdin                                 false
% 7.42/1.49  --stats_out                             all
% 7.42/1.49  
% 7.42/1.49  ------ General Options
% 7.42/1.49  
% 7.42/1.49  --fof                                   false
% 7.42/1.49  --time_out_real                         305.
% 7.42/1.49  --time_out_virtual                      -1.
% 7.42/1.49  --symbol_type_check                     false
% 7.42/1.49  --clausify_out                          false
% 7.42/1.49  --sig_cnt_out                           false
% 7.42/1.49  --trig_cnt_out                          false
% 7.42/1.49  --trig_cnt_out_tolerance                1.
% 7.42/1.49  --trig_cnt_out_sk_spl                   false
% 7.42/1.49  --abstr_cl_out                          false
% 7.42/1.49  
% 7.42/1.49  ------ Global Options
% 7.42/1.49  
% 7.42/1.49  --schedule                              default
% 7.42/1.49  --add_important_lit                     false
% 7.42/1.49  --prop_solver_per_cl                    1000
% 7.42/1.49  --min_unsat_core                        false
% 7.42/1.49  --soft_assumptions                      false
% 7.42/1.49  --soft_lemma_size                       3
% 7.42/1.49  --prop_impl_unit_size                   0
% 7.42/1.49  --prop_impl_unit                        []
% 7.42/1.49  --share_sel_clauses                     true
% 7.42/1.49  --reset_solvers                         false
% 7.42/1.49  --bc_imp_inh                            [conj_cone]
% 7.42/1.49  --conj_cone_tolerance                   3.
% 7.42/1.49  --extra_neg_conj                        none
% 7.42/1.49  --large_theory_mode                     true
% 7.42/1.49  --prolific_symb_bound                   200
% 7.42/1.49  --lt_threshold                          2000
% 7.42/1.49  --clause_weak_htbl                      true
% 7.42/1.49  --gc_record_bc_elim                     false
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing Options
% 7.42/1.49  
% 7.42/1.49  --preprocessing_flag                    true
% 7.42/1.49  --time_out_prep_mult                    0.1
% 7.42/1.49  --splitting_mode                        input
% 7.42/1.49  --splitting_grd                         true
% 7.42/1.49  --splitting_cvd                         false
% 7.42/1.49  --splitting_cvd_svl                     false
% 7.42/1.49  --splitting_nvd                         32
% 7.42/1.49  --sub_typing                            true
% 7.42/1.49  --prep_gs_sim                           true
% 7.42/1.49  --prep_unflatten                        true
% 7.42/1.49  --prep_res_sim                          true
% 7.42/1.49  --prep_upred                            true
% 7.42/1.49  --prep_sem_filter                       exhaustive
% 7.42/1.49  --prep_sem_filter_out                   false
% 7.42/1.49  --pred_elim                             true
% 7.42/1.49  --res_sim_input                         true
% 7.42/1.49  --eq_ax_congr_red                       true
% 7.42/1.49  --pure_diseq_elim                       true
% 7.42/1.49  --brand_transform                       false
% 7.42/1.49  --non_eq_to_eq                          false
% 7.42/1.49  --prep_def_merge                        true
% 7.42/1.49  --prep_def_merge_prop_impl              false
% 7.42/1.49  --prep_def_merge_mbd                    true
% 7.42/1.49  --prep_def_merge_tr_red                 false
% 7.42/1.49  --prep_def_merge_tr_cl                  false
% 7.42/1.49  --smt_preprocessing                     true
% 7.42/1.49  --smt_ac_axioms                         fast
% 7.42/1.49  --preprocessed_out                      false
% 7.42/1.49  --preprocessed_stats                    false
% 7.42/1.49  
% 7.42/1.49  ------ Abstraction refinement Options
% 7.42/1.49  
% 7.42/1.49  --abstr_ref                             []
% 7.42/1.49  --abstr_ref_prep                        false
% 7.42/1.49  --abstr_ref_until_sat                   false
% 7.42/1.49  --abstr_ref_sig_restrict                funpre
% 7.42/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.49  --abstr_ref_under                       []
% 7.42/1.49  
% 7.42/1.49  ------ SAT Options
% 7.42/1.49  
% 7.42/1.49  --sat_mode                              false
% 7.42/1.49  --sat_fm_restart_options                ""
% 7.42/1.49  --sat_gr_def                            false
% 7.42/1.49  --sat_epr_types                         true
% 7.42/1.49  --sat_non_cyclic_types                  false
% 7.42/1.49  --sat_finite_models                     false
% 7.42/1.49  --sat_fm_lemmas                         false
% 7.42/1.49  --sat_fm_prep                           false
% 7.42/1.49  --sat_fm_uc_incr                        true
% 7.42/1.49  --sat_out_model                         small
% 7.42/1.49  --sat_out_clauses                       false
% 7.42/1.49  
% 7.42/1.49  ------ QBF Options
% 7.42/1.49  
% 7.42/1.49  --qbf_mode                              false
% 7.42/1.49  --qbf_elim_univ                         false
% 7.42/1.49  --qbf_dom_inst                          none
% 7.42/1.49  --qbf_dom_pre_inst                      false
% 7.42/1.49  --qbf_sk_in                             false
% 7.42/1.49  --qbf_pred_elim                         true
% 7.42/1.49  --qbf_split                             512
% 7.42/1.49  
% 7.42/1.49  ------ BMC1 Options
% 7.42/1.49  
% 7.42/1.49  --bmc1_incremental                      false
% 7.42/1.49  --bmc1_axioms                           reachable_all
% 7.42/1.49  --bmc1_min_bound                        0
% 7.42/1.49  --bmc1_max_bound                        -1
% 7.42/1.49  --bmc1_max_bound_default                -1
% 7.42/1.49  --bmc1_symbol_reachability              true
% 7.42/1.49  --bmc1_property_lemmas                  false
% 7.42/1.49  --bmc1_k_induction                      false
% 7.42/1.49  --bmc1_non_equiv_states                 false
% 7.42/1.49  --bmc1_deadlock                         false
% 7.42/1.49  --bmc1_ucm                              false
% 7.42/1.49  --bmc1_add_unsat_core                   none
% 7.42/1.49  --bmc1_unsat_core_children              false
% 7.42/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.49  --bmc1_out_stat                         full
% 7.42/1.49  --bmc1_ground_init                      false
% 7.42/1.49  --bmc1_pre_inst_next_state              false
% 7.42/1.49  --bmc1_pre_inst_state                   false
% 7.42/1.49  --bmc1_pre_inst_reach_state             false
% 7.42/1.49  --bmc1_out_unsat_core                   false
% 7.42/1.49  --bmc1_aig_witness_out                  false
% 7.42/1.49  --bmc1_verbose                          false
% 7.42/1.49  --bmc1_dump_clauses_tptp                false
% 7.42/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.49  --bmc1_dump_file                        -
% 7.42/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.49  --bmc1_ucm_extend_mode                  1
% 7.42/1.49  --bmc1_ucm_init_mode                    2
% 7.42/1.49  --bmc1_ucm_cone_mode                    none
% 7.42/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.49  --bmc1_ucm_relax_model                  4
% 7.42/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.49  --bmc1_ucm_layered_model                none
% 7.42/1.49  --bmc1_ucm_max_lemma_size               10
% 7.42/1.49  
% 7.42/1.49  ------ AIG Options
% 7.42/1.49  
% 7.42/1.49  --aig_mode                              false
% 7.42/1.49  
% 7.42/1.49  ------ Instantiation Options
% 7.42/1.49  
% 7.42/1.49  --instantiation_flag                    true
% 7.42/1.49  --inst_sos_flag                         false
% 7.42/1.49  --inst_sos_phase                        true
% 7.42/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.49  --inst_lit_sel_side                     none
% 7.42/1.49  --inst_solver_per_active                1400
% 7.42/1.49  --inst_solver_calls_frac                1.
% 7.42/1.49  --inst_passive_queue_type               priority_queues
% 7.42/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.49  --inst_passive_queues_freq              [25;2]
% 7.42/1.49  --inst_dismatching                      true
% 7.42/1.49  --inst_eager_unprocessed_to_passive     true
% 7.42/1.49  --inst_prop_sim_given                   true
% 7.42/1.49  --inst_prop_sim_new                     false
% 7.42/1.49  --inst_subs_new                         false
% 7.42/1.49  --inst_eq_res_simp                      false
% 7.42/1.49  --inst_subs_given                       false
% 7.42/1.49  --inst_orphan_elimination               true
% 7.42/1.49  --inst_learning_loop_flag               true
% 7.42/1.49  --inst_learning_start                   3000
% 7.42/1.49  --inst_learning_factor                  2
% 7.42/1.49  --inst_start_prop_sim_after_learn       3
% 7.42/1.49  --inst_sel_renew                        solver
% 7.42/1.49  --inst_lit_activity_flag                true
% 7.42/1.49  --inst_restr_to_given                   false
% 7.42/1.49  --inst_activity_threshold               500
% 7.42/1.49  --inst_out_proof                        true
% 7.42/1.49  
% 7.42/1.49  ------ Resolution Options
% 7.42/1.49  
% 7.42/1.49  --resolution_flag                       false
% 7.42/1.49  --res_lit_sel                           adaptive
% 7.42/1.49  --res_lit_sel_side                      none
% 7.42/1.49  --res_ordering                          kbo
% 7.42/1.49  --res_to_prop_solver                    active
% 7.42/1.49  --res_prop_simpl_new                    false
% 7.42/1.49  --res_prop_simpl_given                  true
% 7.42/1.49  --res_passive_queue_type                priority_queues
% 7.42/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.49  --res_passive_queues_freq               [15;5]
% 7.42/1.49  --res_forward_subs                      full
% 7.42/1.49  --res_backward_subs                     full
% 7.42/1.49  --res_forward_subs_resolution           true
% 7.42/1.49  --res_backward_subs_resolution          true
% 7.42/1.49  --res_orphan_elimination                true
% 7.42/1.49  --res_time_limit                        2.
% 7.42/1.49  --res_out_proof                         true
% 7.42/1.49  
% 7.42/1.49  ------ Superposition Options
% 7.42/1.49  
% 7.42/1.49  --superposition_flag                    true
% 7.42/1.49  --sup_passive_queue_type                priority_queues
% 7.42/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.49  --demod_completeness_check              fast
% 7.42/1.49  --demod_use_ground                      true
% 7.42/1.49  --sup_to_prop_solver                    passive
% 7.42/1.49  --sup_prop_simpl_new                    true
% 7.42/1.49  --sup_prop_simpl_given                  true
% 7.42/1.49  --sup_fun_splitting                     false
% 7.42/1.49  --sup_smt_interval                      50000
% 7.42/1.49  
% 7.42/1.49  ------ Superposition Simplification Setup
% 7.42/1.49  
% 7.42/1.49  --sup_indices_passive                   []
% 7.42/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_full_bw                           [BwDemod]
% 7.42/1.49  --sup_immed_triv                        [TrivRules]
% 7.42/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_immed_bw_main                     []
% 7.42/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.49  
% 7.42/1.49  ------ Combination Options
% 7.42/1.49  
% 7.42/1.49  --comb_res_mult                         3
% 7.42/1.49  --comb_sup_mult                         2
% 7.42/1.49  --comb_inst_mult                        10
% 7.42/1.49  
% 7.42/1.49  ------ Debug Options
% 7.42/1.49  
% 7.42/1.49  --dbg_backtrace                         false
% 7.42/1.49  --dbg_dump_prop_clauses                 false
% 7.42/1.49  --dbg_dump_prop_clauses_file            -
% 7.42/1.49  --dbg_out_stat                          false
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  ------ Proving...
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  % SZS status Theorem for theBenchmark.p
% 7.42/1.49  
% 7.42/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.42/1.49  
% 7.42/1.49  fof(f1,axiom,(
% 7.42/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f21,plain,(
% 7.42/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.42/1.49    inference(ennf_transformation,[],[f1])).
% 7.42/1.49  
% 7.42/1.49  fof(f40,plain,(
% 7.42/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.42/1.49    inference(nnf_transformation,[],[f21])).
% 7.42/1.49  
% 7.42/1.49  fof(f41,plain,(
% 7.42/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.42/1.49    inference(rectify,[],[f40])).
% 7.42/1.49  
% 7.42/1.49  fof(f42,plain,(
% 7.42/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.42/1.49    introduced(choice_axiom,[])).
% 7.42/1.49  
% 7.42/1.49  fof(f43,plain,(
% 7.42/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.42/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 7.42/1.49  
% 7.42/1.49  fof(f54,plain,(
% 7.42/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f43])).
% 7.42/1.49  
% 7.42/1.49  fof(f16,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f34,plain,(
% 7.42/1.49    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.42/1.49    inference(ennf_transformation,[],[f16])).
% 7.42/1.49  
% 7.42/1.49  fof(f35,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.42/1.49    inference(flattening,[],[f34])).
% 7.42/1.49  
% 7.42/1.49  fof(f80,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f35])).
% 7.42/1.49  
% 7.42/1.49  fof(f91,plain,(
% 7.42/1.49    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(equality_resolution,[],[f80])).
% 7.42/1.49  
% 7.42/1.49  fof(f17,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f36,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.42/1.49    inference(ennf_transformation,[],[f17])).
% 7.42/1.49  
% 7.42/1.49  fof(f37,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.42/1.49    inference(flattening,[],[f36])).
% 7.42/1.49  
% 7.42/1.49  fof(f82,plain,(
% 7.42/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f37])).
% 7.42/1.49  
% 7.42/1.49  fof(f81,plain,(
% 7.42/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f37])).
% 7.42/1.49  
% 7.42/1.49  fof(f83,plain,(
% 7.42/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f37])).
% 7.42/1.49  
% 7.42/1.49  fof(f5,axiom,(
% 7.42/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f46,plain,(
% 7.42/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.42/1.49    inference(nnf_transformation,[],[f5])).
% 7.42/1.49  
% 7.42/1.49  fof(f47,plain,(
% 7.42/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.42/1.49    inference(flattening,[],[f46])).
% 7.42/1.49  
% 7.42/1.49  fof(f62,plain,(
% 7.42/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.42/1.49    inference(cnf_transformation,[],[f47])).
% 7.42/1.49  
% 7.42/1.49  fof(f90,plain,(
% 7.42/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.42/1.49    inference(equality_resolution,[],[f62])).
% 7.42/1.49  
% 7.42/1.49  fof(f55,plain,(
% 7.42/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f43])).
% 7.42/1.49  
% 7.42/1.49  fof(f3,axiom,(
% 7.42/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f44,plain,(
% 7.42/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.42/1.49    inference(nnf_transformation,[],[f3])).
% 7.42/1.49  
% 7.42/1.49  fof(f45,plain,(
% 7.42/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.42/1.49    inference(flattening,[],[f44])).
% 7.42/1.49  
% 7.42/1.49  fof(f57,plain,(
% 7.42/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.42/1.49    inference(cnf_transformation,[],[f45])).
% 7.42/1.49  
% 7.42/1.49  fof(f88,plain,(
% 7.42/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.42/1.49    inference(equality_resolution,[],[f57])).
% 7.42/1.49  
% 7.42/1.49  fof(f10,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f27,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.42/1.49    inference(ennf_transformation,[],[f10])).
% 7.42/1.49  
% 7.42/1.49  fof(f72,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f27])).
% 7.42/1.49  
% 7.42/1.49  fof(f8,axiom,(
% 7.42/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f49,plain,(
% 7.42/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.42/1.49    inference(nnf_transformation,[],[f8])).
% 7.42/1.49  
% 7.42/1.49  fof(f70,plain,(
% 7.42/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f49])).
% 7.42/1.49  
% 7.42/1.49  fof(f7,axiom,(
% 7.42/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f68,plain,(
% 7.42/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.42/1.49    inference(cnf_transformation,[],[f7])).
% 7.42/1.49  
% 7.42/1.49  fof(f13,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f20,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.42/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.42/1.49  
% 7.42/1.49  fof(f30,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.42/1.49    inference(ennf_transformation,[],[f20])).
% 7.42/1.49  
% 7.42/1.49  fof(f76,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.42/1.49    inference(cnf_transformation,[],[f30])).
% 7.42/1.49  
% 7.42/1.49  fof(f11,axiom,(
% 7.42/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f28,plain,(
% 7.42/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.42/1.49    inference(ennf_transformation,[],[f11])).
% 7.42/1.49  
% 7.42/1.49  fof(f50,plain,(
% 7.42/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.42/1.49    inference(nnf_transformation,[],[f28])).
% 7.42/1.49  
% 7.42/1.49  fof(f73,plain,(
% 7.42/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f50])).
% 7.42/1.49  
% 7.42/1.49  fof(f12,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f29,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.42/1.49    inference(ennf_transformation,[],[f12])).
% 7.42/1.49  
% 7.42/1.49  fof(f75,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.42/1.49    inference(cnf_transformation,[],[f29])).
% 7.42/1.49  
% 7.42/1.49  fof(f69,plain,(
% 7.42/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.42/1.49    inference(cnf_transformation,[],[f49])).
% 7.42/1.49  
% 7.42/1.49  fof(f59,plain,(
% 7.42/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f45])).
% 7.42/1.49  
% 7.42/1.49  fof(f18,conjecture,(
% 7.42/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f19,negated_conjecture,(
% 7.42/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 7.42/1.49    inference(negated_conjecture,[],[f18])).
% 7.42/1.49  
% 7.42/1.49  fof(f38,plain,(
% 7.42/1.49    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.42/1.49    inference(ennf_transformation,[],[f19])).
% 7.42/1.49  
% 7.42/1.49  fof(f39,plain,(
% 7.42/1.49    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.42/1.49    inference(flattening,[],[f38])).
% 7.42/1.49  
% 7.42/1.49  fof(f51,plain,(
% 7.42/1.49    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 7.42/1.49    introduced(choice_axiom,[])).
% 7.42/1.49  
% 7.42/1.49  fof(f52,plain,(
% 7.42/1.49    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 7.42/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f51])).
% 7.42/1.49  
% 7.42/1.49  fof(f85,plain,(
% 7.42/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.42/1.49    inference(cnf_transformation,[],[f52])).
% 7.42/1.49  
% 7.42/1.49  fof(f79,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f35])).
% 7.42/1.49  
% 7.42/1.49  fof(f84,plain,(
% 7.42/1.49    v1_funct_1(sK3)),
% 7.42/1.49    inference(cnf_transformation,[],[f52])).
% 7.42/1.49  
% 7.42/1.49  fof(f86,plain,(
% 7.42/1.49    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))),
% 7.42/1.49    inference(cnf_transformation,[],[f52])).
% 7.42/1.49  
% 7.42/1.49  fof(f63,plain,(
% 7.42/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.42/1.49    inference(cnf_transformation,[],[f47])).
% 7.42/1.49  
% 7.42/1.49  fof(f89,plain,(
% 7.42/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.42/1.49    inference(equality_resolution,[],[f63])).
% 7.42/1.49  
% 7.42/1.49  fof(f61,plain,(
% 7.42/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f47])).
% 7.42/1.49  
% 7.42/1.49  fof(f15,axiom,(
% 7.42/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f32,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.42/1.49    inference(ennf_transformation,[],[f15])).
% 7.42/1.49  
% 7.42/1.49  fof(f33,plain,(
% 7.42/1.49    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.42/1.49    inference(flattening,[],[f32])).
% 7.42/1.49  
% 7.42/1.49  fof(f78,plain,(
% 7.42/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.42/1.49    inference(cnf_transformation,[],[f33])).
% 7.42/1.49  
% 7.42/1.49  fof(f2,axiom,(
% 7.42/1.49    v1_xboole_0(k1_xboole_0)),
% 7.42/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.42/1.49  
% 7.42/1.49  fof(f56,plain,(
% 7.42/1.49    v1_xboole_0(k1_xboole_0)),
% 7.42/1.49    inference(cnf_transformation,[],[f2])).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1,plain,
% 7.42/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.42/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1356,plain,
% 7.42/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.42/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_26,plain,
% 7.42/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.42/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.42/1.49      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 7.42/1.49      | ~ v1_funct_1(X0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_29,plain,
% 7.42/1.49      ( v1_funct_2(X0,X1,X2)
% 7.42/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 7.42/1.49      | ~ v1_funct_1(X3) ),
% 7.42/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_475,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 7.42/1.49      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
% 7.42/1.49      | ~ v1_funct_1(X3)
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | X5 != X3
% 7.42/1.49      | X2 != X4
% 7.42/1.49      | k1_xboole_0 != X1 ),
% 7.42/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_476,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.42/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.42/1.49      | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
% 7.42/1.49      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | ~ v1_funct_1(X2) ),
% 7.42/1.49      inference(unflattening,[status(thm)],[c_475]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_30,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | v1_funct_1(X3) ),
% 7.42/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_28,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | ~ v1_funct_1(X0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_492,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.42/1.49      | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
% 7.42/1.49      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
% 7.42/1.49      | ~ v1_funct_1(X0) ),
% 7.42/1.49      inference(forward_subsumption_resolution,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_476,c_30,c_28]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1332,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 7.42/1.49      | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
% 7.42/1.49      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_9,plain,
% 7.42/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.42/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1468,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
% 7.42/1.49      | r2_hidden(X1,k1_funct_2(k1_xboole_0,X2)) = iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_1332,c_9]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_5265,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | r2_hidden(sK0(k5_partfun1(k1_xboole_0,X1,X0),X2),k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 7.42/1.49      | r1_tarski(k5_partfun1(k1_xboole_0,X1,X0),X2) = iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1356,c_1468]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_0,plain,
% 7.42/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.42/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1357,plain,
% 7.42/1.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.42/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_46313,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | r1_tarski(k5_partfun1(k1_xboole_0,X1,X0),k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_5265,c_1357]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_46378,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.42/1.49      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_46313]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_6,plain,
% 7.42/1.49      ( r1_tarski(X0,X0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1352,plain,
% 7.42/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_19,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.42/1.49      | ~ r2_hidden(X2,X0)
% 7.42/1.49      | ~ v1_xboole_0(X1) ),
% 7.42/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_16,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.42/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_232,plain,
% 7.42/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.42/1.49      inference(prop_impl,[status(thm)],[c_16]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_233,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.42/1.49      inference(renaming,[status(thm)],[c_232]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_292,plain,
% 7.42/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.42/1.49      inference(bin_hyper_res,[status(thm)],[c_19,c_233]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1335,plain,
% 7.42/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.42/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.42/1.49      | v1_xboole_0(X2) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3193,plain,
% 7.42/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.42/1.49      | r1_tarski(X0,X2) = iProver_top
% 7.42/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1356,c_1335]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_8584,plain,
% 7.42/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1352,c_3193]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_15,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.42/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1346,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_23,plain,
% 7.42/1.49      ( v4_relat_1(X0,X1)
% 7.42/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.42/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_21,plain,
% 7.42/1.49      ( ~ v4_relat_1(X0,X1)
% 7.42/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.42/1.49      | ~ v1_relat_1(X0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_430,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.42/1.49      | ~ v1_relat_1(X0) ),
% 7.42/1.49      inference(resolution,[status(thm)],[c_23,c_21]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_22,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | v1_relat_1(X0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_434,plain,
% 7.42/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 7.42/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_430,c_22]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_435,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.42/1.49      inference(renaming,[status(thm)],[c_434]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1334,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.42/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2118,plain,
% 7.42/1.49      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1346,c_1334]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_17,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.42/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1344,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.42/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1746,plain,
% 7.42/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1346,c_1344]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_4,plain,
% 7.42/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.42/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1353,plain,
% 7.42/1.49      ( X0 = X1
% 7.42/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.42/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3354,plain,
% 7.42/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1746,c_1353]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_4241,plain,
% 7.42/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_2118,c_3354]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_32,negated_conjecture,
% 7.42/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.42/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1337,plain,
% 7.42/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_27,plain,
% 7.42/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.42/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | r2_hidden(X0,k1_funct_2(X1,X2))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | k1_xboole_0 = X2 ),
% 7.42/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_451,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | r2_hidden(X3,k1_funct_2(X1,X2))
% 7.42/1.49      | ~ v1_funct_1(X3)
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | k1_xboole_0 = X2 ),
% 7.42/1.49      inference(resolution,[status(thm)],[c_29,c_27]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_455,plain,
% 7.42/1.49      ( r2_hidden(X3,k1_funct_2(X1,X2))
% 7.42/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | k1_xboole_0 = X2 ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_451,c_30,c_28]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_456,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.42/1.49      | r2_hidden(X3,k1_funct_2(X1,X2))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | k1_xboole_0 = X2 ),
% 7.42/1.49      inference(renaming,[status(thm)],[c_455]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1333,plain,
% 7.42/1.49      ( k1_xboole_0 = X0
% 7.42/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.42/1.49      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 7.42/1.49      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 7.42/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2288,plain,
% 7.42/1.49      ( sK2 = k1_xboole_0
% 7.42/1.49      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 7.42/1.49      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 7.42/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1337,c_1333]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_33,negated_conjecture,
% 7.42/1.49      ( v1_funct_1(sK3) ),
% 7.42/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_34,plain,
% 7.42/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2740,plain,
% 7.42/1.49      ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 7.42/1.49      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 7.42/1.49      | sK2 = k1_xboole_0 ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_2288,c_34]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2741,plain,
% 7.42/1.49      ( sK2 = k1_xboole_0
% 7.42/1.49      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 7.42/1.49      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
% 7.42/1.49      inference(renaming,[status(thm)],[c_2740]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2749,plain,
% 7.42/1.49      ( sK2 = k1_xboole_0
% 7.42/1.49      | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
% 7.42/1.49      | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1356,c_2741]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2757,plain,
% 7.42/1.49      ( sK2 = k1_xboole_0
% 7.42/1.49      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_2749,c_1357]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_31,negated_conjecture,
% 7.42/1.49      ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
% 7.42/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_36,plain,
% 7.42/1.49      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2932,plain,
% 7.42/1.49      ( sK2 = k1_xboole_0 ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_2757,c_36]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1747,plain,
% 7.42/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1337,c_1344]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2937,plain,
% 7.42/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_2932,c_1747]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_8,plain,
% 7.42/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.42/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2946,plain,
% 7.42/1.49      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_2937,c_8]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3357,plain,
% 7.42/1.49      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_2946,c_1353]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3545,plain,
% 7.42/1.49      ( sK3 = k1_xboole_0 ),
% 7.42/1.49      inference(forward_subsumption_resolution,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_3357,c_1746]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2120,plain,
% 7.42/1.49      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_1337,c_1334]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3356,plain,
% 7.42/1.49      ( k1_relat_1(sK3) = sK1
% 7.42/1.49      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_2120,c_1353]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3547,plain,
% 7.42/1.49      ( k1_relat_1(k1_xboole_0) = sK1
% 7.42/1.49      | r1_tarski(sK1,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_3545,c_3356]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_4432,plain,
% 7.42/1.49      ( sK1 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_4241,c_3547]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_8782,plain,
% 7.42/1.49      ( sK1 = k1_xboole_0 | v1_xboole_0(sK1) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_8584,c_4432]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_74,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_76,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_74]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_10,plain,
% 7.42/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.42/1.49      | k1_xboole_0 = X1
% 7.42/1.49      | k1_xboole_0 = X0 ),
% 7.42/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_87,plain,
% 7.42/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.42/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_88,plain,
% 7.42/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_743,plain,
% 7.42/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.42/1.49      theory(equality) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1571,plain,
% 7.42/1.49      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1572,plain,
% 7.42/1.49      ( X0 != sK3
% 7.42/1.49      | v1_funct_1(X0) = iProver_top
% 7.42/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1574,plain,
% 7.42/1.49      ( k1_xboole_0 != sK3
% 7.42/1.49      | v1_funct_1(sK3) != iProver_top
% 7.42/1.49      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_1572]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_735,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1680,plain,
% 7.42/1.49      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_735]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1681,plain,
% 7.42/1.49      ( sK3 != k1_xboole_0
% 7.42/1.49      | k1_xboole_0 = sK3
% 7.42/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.42/1.49      inference(instantiation,[status(thm)],[c_1680]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_25,plain,
% 7.42/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.42/1.49      | ~ v1_funct_1(X0)
% 7.42/1.49      | ~ v1_xboole_0(X2)
% 7.42/1.49      | v1_xboole_0(X1)
% 7.42/1.49      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 7.42/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1341,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top
% 7.42/1.49      | v1_xboole_0(X2) != iProver_top
% 7.42/1.49      | v1_xboole_0(X1) = iProver_top
% 7.42/1.49      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_5214,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top
% 7.42/1.49      | v1_xboole_0(X1) = iProver_top
% 7.42/1.49      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 7.42/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_8,c_1341]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3,plain,
% 7.42/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.42/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_97,plain,
% 7.42/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_5491,plain,
% 7.42/1.49      ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 7.42/1.49      | v1_xboole_0(X1) = iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top
% 7.42/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_5214,c_97]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_5492,plain,
% 7.42/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | v1_funct_1(X0) != iProver_top
% 7.42/1.49      | v1_xboole_0(X1) = iProver_top
% 7.42/1.49      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
% 7.42/1.49      inference(renaming,[status(thm)],[c_5491]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_1338,plain,
% 7.42/1.49      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 7.42/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_2938,plain,
% 7.42/1.49      ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,sK3),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_2932,c_1338]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_3552,plain,
% 7.42/1.49      ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_3545,c_2938]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_8785,plain,
% 7.42/1.49      ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_8584,c_3552]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_8922,plain,
% 7.42/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.42/1.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.42/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.42/1.49      inference(superposition,[status(thm)],[c_5492,c_8785]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_9072,plain,
% 7.42/1.49      ( sK1 = k1_xboole_0 ),
% 7.42/1.49      inference(global_propositional_subsumption,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_8782,c_34,c_76,c_87,c_88,c_1574,c_1681,c_3545,c_8922]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(c_9077,plain,
% 7.42/1.49      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.42/1.49      inference(demodulation,[status(thm)],[c_9072,c_3552]) ).
% 7.42/1.49  
% 7.42/1.49  cnf(contradiction,plain,
% 7.42/1.49      ( $false ),
% 7.42/1.49      inference(minisat,
% 7.42/1.49                [status(thm)],
% 7.42/1.49                [c_46378,c_9077,c_3545,c_1681,c_1574,c_88,c_87,c_76,c_34]) ).
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.42/1.49  
% 7.42/1.49  ------                               Statistics
% 7.42/1.49  
% 7.42/1.49  ------ General
% 7.42/1.49  
% 7.42/1.49  abstr_ref_over_cycles:                  0
% 7.42/1.49  abstr_ref_under_cycles:                 0
% 7.42/1.49  gc_basic_clause_elim:                   0
% 7.42/1.49  forced_gc_time:                         0
% 7.42/1.49  parsing_time:                           0.009
% 7.42/1.49  unif_index_cands_time:                  0.
% 7.42/1.49  unif_index_add_time:                    0.
% 7.42/1.49  orderings_time:                         0.
% 7.42/1.49  out_proof_time:                         0.013
% 7.42/1.49  total_time:                             0.976
% 7.42/1.49  num_of_symbols:                         49
% 7.42/1.49  num_of_terms:                           31864
% 7.42/1.49  
% 7.42/1.49  ------ Preprocessing
% 7.42/1.49  
% 7.42/1.49  num_of_splits:                          0
% 7.42/1.49  num_of_split_atoms:                     0
% 7.42/1.49  num_of_reused_defs:                     0
% 7.42/1.49  num_eq_ax_congr_red:                    14
% 7.42/1.49  num_of_sem_filtered_clauses:            1
% 7.42/1.49  num_of_subtypes:                        0
% 7.42/1.49  monotx_restored_types:                  0
% 7.42/1.49  sat_num_of_epr_types:                   0
% 7.42/1.49  sat_num_of_non_cyclic_types:            0
% 7.42/1.49  sat_guarded_non_collapsed_types:        0
% 7.42/1.49  num_pure_diseq_elim:                    0
% 7.42/1.49  simp_replaced_by:                       0
% 7.42/1.49  res_preprocessed:                       143
% 7.42/1.49  prep_upred:                             0
% 7.42/1.49  prep_unflattend:                        3
% 7.42/1.49  smt_new_axioms:                         0
% 7.42/1.49  pred_elim_cands:                        5
% 7.42/1.49  pred_elim:                              3
% 7.42/1.49  pred_elim_cl:                           4
% 7.42/1.49  pred_elim_cycles:                       6
% 7.42/1.49  merged_defs:                            8
% 7.42/1.49  merged_defs_ncl:                        0
% 7.42/1.49  bin_hyper_res:                          9
% 7.42/1.49  prep_cycles:                            4
% 7.42/1.49  pred_elim_time:                         0.003
% 7.42/1.49  splitting_time:                         0.
% 7.42/1.49  sem_filter_time:                        0.
% 7.42/1.49  monotx_time:                            0.
% 7.42/1.49  subtype_inf_time:                       0.
% 7.42/1.49  
% 7.42/1.49  ------ Problem properties
% 7.42/1.49  
% 7.42/1.49  clauses:                                29
% 7.42/1.49  conjectures:                            3
% 7.42/1.49  epr:                                    11
% 7.42/1.49  horn:                                   23
% 7.42/1.49  ground:                                 4
% 7.42/1.49  unary:                                  8
% 7.42/1.49  binary:                                 5
% 7.42/1.49  lits:                                   73
% 7.42/1.49  lits_eq:                                7
% 7.42/1.49  fd_pure:                                0
% 7.42/1.49  fd_pseudo:                              0
% 7.42/1.49  fd_cond:                                2
% 7.42/1.49  fd_pseudo_cond:                         1
% 7.42/1.49  ac_symbols:                             0
% 7.42/1.49  
% 7.42/1.49  ------ Propositional Solver
% 7.42/1.49  
% 7.42/1.49  prop_solver_calls:                      32
% 7.42/1.49  prop_fast_solver_calls:                 1530
% 7.42/1.49  smt_solver_calls:                       0
% 7.42/1.49  smt_fast_solver_calls:                  0
% 7.42/1.49  prop_num_of_clauses:                    15829
% 7.42/1.49  prop_preprocess_simplified:             23939
% 7.42/1.49  prop_fo_subsumed:                       16
% 7.42/1.49  prop_solver_time:                       0.
% 7.42/1.49  smt_solver_time:                        0.
% 7.42/1.49  smt_fast_solver_time:                   0.
% 7.42/1.49  prop_fast_solver_time:                  0.
% 7.42/1.49  prop_unsat_core_time:                   0.001
% 7.42/1.49  
% 7.42/1.49  ------ QBF
% 7.42/1.49  
% 7.42/1.49  qbf_q_res:                              0
% 7.42/1.49  qbf_num_tautologies:                    0
% 7.42/1.49  qbf_prep_cycles:                        0
% 7.42/1.49  
% 7.42/1.49  ------ BMC1
% 7.42/1.49  
% 7.42/1.49  bmc1_current_bound:                     -1
% 7.42/1.49  bmc1_last_solved_bound:                 -1
% 7.42/1.49  bmc1_unsat_core_size:                   -1
% 7.42/1.49  bmc1_unsat_core_parents_size:           -1
% 7.42/1.49  bmc1_merge_next_fun:                    0
% 7.42/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.42/1.49  
% 7.42/1.49  ------ Instantiation
% 7.42/1.49  
% 7.42/1.49  inst_num_of_clauses:                    2840
% 7.42/1.49  inst_num_in_passive:                    1535
% 7.42/1.49  inst_num_in_active:                     1217
% 7.42/1.49  inst_num_in_unprocessed:                88
% 7.42/1.49  inst_num_of_loops:                      1480
% 7.42/1.49  inst_num_of_learning_restarts:          0
% 7.42/1.49  inst_num_moves_active_passive:          259
% 7.42/1.49  inst_lit_activity:                      0
% 7.42/1.49  inst_lit_activity_moves:                0
% 7.42/1.49  inst_num_tautologies:                   0
% 7.42/1.49  inst_num_prop_implied:                  0
% 7.42/1.49  inst_num_existing_simplified:           0
% 7.42/1.49  inst_num_eq_res_simplified:             0
% 7.42/1.49  inst_num_child_elim:                    0
% 7.42/1.49  inst_num_of_dismatching_blockings:      2348
% 7.42/1.49  inst_num_of_non_proper_insts:           3383
% 7.42/1.49  inst_num_of_duplicates:                 0
% 7.42/1.49  inst_inst_num_from_inst_to_res:         0
% 7.42/1.49  inst_dismatching_checking_time:         0.
% 7.42/1.49  
% 7.42/1.49  ------ Resolution
% 7.42/1.49  
% 7.42/1.49  res_num_of_clauses:                     0
% 7.42/1.49  res_num_in_passive:                     0
% 7.42/1.49  res_num_in_active:                      0
% 7.42/1.49  res_num_of_loops:                       147
% 7.42/1.49  res_forward_subset_subsumed:            288
% 7.42/1.49  res_backward_subset_subsumed:           0
% 7.42/1.49  res_forward_subsumed:                   0
% 7.42/1.49  res_backward_subsumed:                  0
% 7.42/1.49  res_forward_subsumption_resolution:     2
% 7.42/1.49  res_backward_subsumption_resolution:    0
% 7.42/1.49  res_clause_to_clause_subsumption:       16227
% 7.42/1.49  res_orphan_elimination:                 0
% 7.42/1.49  res_tautology_del:                      401
% 7.42/1.49  res_num_eq_res_simplified:              0
% 7.42/1.49  res_num_sel_changes:                    0
% 7.42/1.49  res_moves_from_active_to_pass:          0
% 7.42/1.49  
% 7.42/1.49  ------ Superposition
% 7.42/1.49  
% 7.42/1.49  sup_time_total:                         0.
% 7.42/1.49  sup_time_generating:                    0.
% 7.42/1.49  sup_time_sim_full:                      0.
% 7.42/1.49  sup_time_sim_immed:                     0.
% 7.42/1.49  
% 7.42/1.49  sup_num_of_clauses:                     2267
% 7.42/1.49  sup_num_in_active:                      270
% 7.42/1.49  sup_num_in_passive:                     1997
% 7.42/1.49  sup_num_of_loops:                       295
% 7.42/1.49  sup_fw_superposition:                   1796
% 7.42/1.49  sup_bw_superposition:                   1560
% 7.42/1.49  sup_immediate_simplified:               397
% 7.42/1.49  sup_given_eliminated:                   3
% 7.42/1.49  comparisons_done:                       0
% 7.42/1.49  comparisons_avoided:                    0
% 7.42/1.49  
% 7.42/1.49  ------ Simplifications
% 7.42/1.49  
% 7.42/1.49  
% 7.42/1.49  sim_fw_subset_subsumed:                 54
% 7.42/1.49  sim_bw_subset_subsumed:                 11
% 7.42/1.49  sim_fw_subsumed:                        96
% 7.42/1.49  sim_bw_subsumed:                        12
% 7.42/1.49  sim_fw_subsumption_res:                 7
% 7.42/1.49  sim_bw_subsumption_res:                 0
% 7.42/1.49  sim_tautology_del:                      28
% 7.42/1.49  sim_eq_tautology_del:                   148
% 7.42/1.49  sim_eq_res_simp:                        0
% 7.42/1.49  sim_fw_demodulated:                     120
% 7.42/1.49  sim_bw_demodulated:                     19
% 7.42/1.49  sim_light_normalised:                   239
% 7.42/1.49  sim_joinable_taut:                      0
% 7.42/1.49  sim_joinable_simp:                      0
% 7.42/1.49  sim_ac_normalised:                      0
% 7.42/1.49  sim_smt_subsumption:                    0
% 7.42/1.49  
%------------------------------------------------------------------------------
