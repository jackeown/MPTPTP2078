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
% DateTime   : Thu Dec  3 12:09:25 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 270 expanded)
%              Number of clauses        :   63 (  74 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 (1466 expanded)
%              Number of equality atoms :  133 ( 317 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
          & m1_subset_1(X3,X0) )
     => ( k7_partfun1(X1,X2,sK4) != k3_funct_2(X0,X1,X2,sK4)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( k7_partfun1(X1,sK3,X3) != k3_funct_2(X0,X1,sK3,X3)
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k7_partfun1(sK2,X2,X3) != k3_funct_2(X0,sK2,X2,X3)
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_2(X2,X0,sK2)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK1,X1,X2,X3)
                  & m1_subset_1(X3,sK1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X2,sK1,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4)
    & m1_subset_1(sK4,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f52,f51,f50,f49])).

fof(f85,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f34])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1959,plain,
    ( m1_subset_1(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1963,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3611,plain,
    ( r2_hidden(sK4,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1963])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2232,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2346,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK4,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_2347,plain,
    ( m1_subset_1(sK4,sK1) != iProver_top
    | r2_hidden(sK4,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_3892,plain,
    ( r2_hidden(sK4,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3611,c_33,c_38,c_2347])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK3 != X0
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_760,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_28])).

cnf(c_1958,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1960,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2932,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1958,c_1960])).

cnf(c_3066,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_760,c_2932])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_13,c_24])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_363,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_12])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_1953,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_4327,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_1953])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4358,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_35])).

cnf(c_4359,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4358])).

cnf(c_4367,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_4359])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1522,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2212,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1522])).

cnf(c_2213,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_2215,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1967,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1965,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_1954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_2715,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1954])).

cnf(c_3389,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_2715])).

cnf(c_4445,plain,
    ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4367,c_34,c_2215,c_3389])).

cnf(c_4454,plain,
    ( k7_partfun1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3892,c_4445])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK1 != X1
    | sK3 != X2
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_32,c_30,c_28])).

cnf(c_1946,plain,
    ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_2344,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1959,c_1946])).

cnf(c_26,negated_conjecture,
    ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2477,plain,
    ( k7_partfun1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2344,c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4454,c_2477])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.00  
% 2.32/1.00  ------  iProver source info
% 2.32/1.00  
% 2.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.00  git: non_committed_changes: false
% 2.32/1.00  git: last_make_outside_of_git: false
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     num_symb
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       true
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 29
% 2.32/1.00  conjectures                             6
% 2.32/1.00  EPR                                     8
% 2.32/1.00  Horn                                    19
% 2.32/1.00  unary                                   10
% 2.32/1.00  binary                                  7
% 2.32/1.00  lits                                    76
% 2.32/1.00  lits eq                                 26
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 4
% 2.32/1.00  fd_pseudo_cond                          0
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status Theorem for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f17,conjecture,(
% 2.32/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3)))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f18,negated_conjecture,(
% 2.32/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3)))))),
% 2.32/1.00    inference(negated_conjecture,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f40,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.32/1.00    inference(flattening,[],[f40])).
% 2.32/1.00  
% 2.32/1.00  fof(f52,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) => (k7_partfun1(X1,X2,sK4) != k3_funct_2(X0,X1,X2,sK4) & m1_subset_1(sK4,X0))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k7_partfun1(X1,sK3,X3) != k3_funct_2(X0,X1,sK3,X3) & m1_subset_1(X3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (k7_partfun1(sK2,X2,X3) != k3_funct_2(X0,sK2,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK1,X1,X2,X3) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    (((k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) & m1_subset_1(sK4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f52,f51,f50,f49])).
% 2.32/1.00  
% 2.32/1.00  fof(f85,plain,(
% 2.32/1.00    m1_subset_1(sK4,sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.32/1.00    inference(ennf_transformation,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.32/1.00    inference(flattening,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f61,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f80,plain,(
% 2.32/1.00    ~v1_xboole_0(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f14,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(ennf_transformation,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(flattening,[],[f34])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(nnf_transformation,[],[f35])).
% 2.32/1.00  
% 2.32/1.00  fof(f72,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f83,plain,(
% 2.32/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f84,plain,(
% 2.32/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f12,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f31,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(ennf_transformation,[],[f12])).
% 2.32/1.00  
% 2.32/1.00  fof(f68,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f31])).
% 2.32/1.00  
% 2.32/1.00  fof(f11,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(ennf_transformation,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f67,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f30])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,axiom,(
% 2.32/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f36,plain,(
% 2.32/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.32/1.00    inference(ennf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f37,plain,(
% 2.32/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.32/1.00    inference(flattening,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f78,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f37])).
% 2.32/1.00  
% 2.32/1.00  fof(f10,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(ennf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f66,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f82,plain,(
% 2.32/1.00    v1_funct_1(sK3)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f81,plain,(
% 2.32/1.00    ~v1_xboole_0(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f42,plain,(
% 2.32/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.32/1.00    inference(nnf_transformation,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/1.00    inference(rectify,[],[f42])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f45])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f59,plain,(
% 2.32/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.32/1.00    inference(unused_predicate_definition_removal,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.32/1.00    inference(ennf_transformation,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f62,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f9,axiom,(
% 2.32/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.32/1.00    inference(ennf_transformation,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f65,plain,(
% 2.32/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f16,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f38,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.32/1.00    inference(flattening,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f79,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f39])).
% 2.32/1.00  
% 2.32/1.00  fof(f86,plain,(
% 2.32/1.00    k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4)),
% 2.32/1.00    inference(cnf_transformation,[],[f53])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_27,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK4,sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1959,plain,
% 2.32/1.00      ( m1_subset_1(sK4,sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1963,plain,
% 2.32/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.32/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.32/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3611,plain,
% 2.32/1.00      ( r2_hidden(sK4,sK1) = iProver_top
% 2.32/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1959,c_1963]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_32,negated_conjecture,
% 2.32/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_33,plain,
% 2.32/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_38,plain,
% 2.32/1.00      ( m1_subset_1(sK4,sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2232,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | v1_xboole_0(sK1) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2346,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK4,sK1) | r2_hidden(sK4,sK1) | v1_xboole_0(sK1) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2232]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2347,plain,
% 2.32/1.00      ( m1_subset_1(sK4,sK1) != iProver_top
% 2.32/1.00      | r2_hidden(sK4,sK1) = iProver_top
% 2.32/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2346]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3892,plain,
% 2.32/1.00      ( r2_hidden(sK4,sK1) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3611,c_33,c_38,c_2347]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_23,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.32/1.00      | k1_xboole_0 = X2 ),
% 2.32/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_29,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_757,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.32/1.00      | sK1 != X1
% 2.32/1.00      | sK3 != X0
% 2.32/1.00      | sK2 != X2
% 2.32/1.00      | k1_xboole_0 = X2 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_758,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.32/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.32/1.00      | k1_xboole_0 = sK2 ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_757]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_28,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_760,plain,
% 2.32/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_758,c_28]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1958,plain,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1960,plain,
% 2.32/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2932,plain,
% 2.32/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1958,c_1960]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3066,plain,
% 2.32/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_760,c_2932]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,plain,
% 2.32/1.00      ( v5_relat_1(X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_24,plain,
% 2.32/1.00      ( ~ v5_relat_1(X0,X1)
% 2.32/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.32/1.00      | ~ v1_relat_1(X0)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_359,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.32/1.00      | ~ v1_relat_1(X0)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_13,c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | v1_relat_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_363,plain,
% 2.32/1.00      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_359,c_12]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_364,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_363]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1953,plain,
% 2.32/1.00      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.32/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.32/1.00      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.32/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4327,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.32/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.32/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1958,c_1953]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_30,negated_conjecture,
% 2.32/1.00      ( v1_funct_1(sK3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_35,plain,
% 2.32/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4358,plain,
% 2.32/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.32/1.00      | k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4327,c_35]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4359,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.32/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_4358]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4367,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.32/1.00      | sK2 = k1_xboole_0
% 2.32/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3066,c_4359]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_31,negated_conjecture,
% 2.32/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_34,plain,
% 2.32/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1522,plain,
% 2.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2212,plain,
% 2.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1522]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2213,plain,
% 2.32/1.00      ( sK2 != X0
% 2.32/1.00      | v1_xboole_0(X0) != iProver_top
% 2.32/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2215,plain,
% 2.32/1.00      ( sK2 != k1_xboole_0
% 2.32/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.32/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2213]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1967,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.32/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5,plain,
% 2.32/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1965,plain,
% 2.32/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_8,plain,
% 2.32/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_11,plain,
% 2.32/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_320,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1954,plain,
% 2.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.32/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2715,plain,
% 2.32/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1965,c_1954]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3389,plain,
% 2.32/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1967,c_2715]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4445,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.32/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4367,c_34,c_2215,c_3389]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4454,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3892,c_4445]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_25,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | v1_xboole_0(X1)
% 2.32/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_739,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.32/1.00      | ~ v1_funct_1(X2)
% 2.32/1.00      | v1_xboole_0(X1)
% 2.32/1.00      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.32/1.00      | sK1 != X1
% 2.32/1.00      | sK3 != X2
% 2.32/1.00      | sK2 != X3 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_740,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,sK1)
% 2.32/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.32/1.00      | ~ v1_funct_1(sK3)
% 2.32/1.00      | v1_xboole_0(sK1)
% 2.32/1.00      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_739]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_744,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,sK1)
% 2.32/1.00      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_740,c_32,c_30,c_28]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1946,plain,
% 2.32/1.00      ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
% 2.32/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2344,plain,
% 2.32/1.00      ( k3_funct_2(sK1,sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1959,c_1946]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_26,negated_conjecture,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,sK4) != k3_funct_2(sK1,sK2,sK3,sK4) ),
% 2.32/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2477,plain,
% 2.32/1.00      ( k7_partfun1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4) ),
% 2.32/1.00      inference(demodulation,[status(thm)],[c_2344,c_26]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(contradiction,plain,
% 2.32/1.00      ( $false ),
% 2.32/1.00      inference(minisat,[status(thm)],[c_4454,c_2477]) ).
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  ------                               Statistics
% 2.32/1.00  
% 2.32/1.00  ------ General
% 2.32/1.00  
% 2.32/1.00  abstr_ref_over_cycles:                  0
% 2.32/1.00  abstr_ref_under_cycles:                 0
% 2.32/1.00  gc_basic_clause_elim:                   0
% 2.32/1.00  forced_gc_time:                         0
% 2.32/1.00  parsing_time:                           0.011
% 2.32/1.00  unif_index_cands_time:                  0.
% 2.32/1.00  unif_index_add_time:                    0.
% 2.32/1.00  orderings_time:                         0.
% 2.32/1.00  out_proof_time:                         0.011
% 2.32/1.00  total_time:                             0.193
% 2.32/1.00  num_of_symbols:                         52
% 2.32/1.00  num_of_terms:                           3887
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing
% 2.32/1.00  
% 2.32/1.00  num_of_splits:                          0
% 2.32/1.00  num_of_split_atoms:                     0
% 2.32/1.00  num_of_reused_defs:                     0
% 2.32/1.00  num_eq_ax_congr_red:                    17
% 2.32/1.00  num_of_sem_filtered_clauses:            1
% 2.32/1.00  num_of_subtypes:                        0
% 2.32/1.00  monotx_restored_types:                  0
% 2.32/1.00  sat_num_of_epr_types:                   0
% 2.32/1.00  sat_num_of_non_cyclic_types:            0
% 2.32/1.00  sat_guarded_non_collapsed_types:        0
% 2.32/1.00  num_pure_diseq_elim:                    0
% 2.32/1.00  simp_replaced_by:                       0
% 2.32/1.00  res_preprocessed:                       143
% 2.32/1.00  prep_upred:                             0
% 2.32/1.00  prep_unflattend:                        85
% 2.32/1.00  smt_new_axioms:                         0
% 2.32/1.00  pred_elim_cands:                        4
% 2.32/1.00  pred_elim:                              4
% 2.32/1.00  pred_elim_cl:                           2
% 2.32/1.00  pred_elim_cycles:                       10
% 2.32/1.00  merged_defs:                            0
% 2.32/1.00  merged_defs_ncl:                        0
% 2.32/1.00  bin_hyper_res:                          0
% 2.32/1.00  prep_cycles:                            4
% 2.32/1.00  pred_elim_time:                         0.021
% 2.32/1.00  splitting_time:                         0.
% 2.32/1.00  sem_filter_time:                        0.
% 2.32/1.00  monotx_time:                            0.
% 2.32/1.00  subtype_inf_time:                       0.
% 2.32/1.00  
% 2.32/1.00  ------ Problem properties
% 2.32/1.00  
% 2.32/1.00  clauses:                                29
% 2.32/1.00  conjectures:                            6
% 2.32/1.00  epr:                                    8
% 2.32/1.00  horn:                                   19
% 2.32/1.00  ground:                                 10
% 2.32/1.00  unary:                                  10
% 2.32/1.00  binary:                                 7
% 2.32/1.00  lits:                                   76
% 2.32/1.00  lits_eq:                                26
% 2.32/1.00  fd_pure:                                0
% 2.32/1.00  fd_pseudo:                              0
% 2.32/1.00  fd_cond:                                4
% 2.32/1.00  fd_pseudo_cond:                         0
% 2.32/1.00  ac_symbols:                             0
% 2.32/1.00  
% 2.32/1.00  ------ Propositional Solver
% 2.32/1.00  
% 2.32/1.00  prop_solver_calls:                      28
% 2.32/1.00  prop_fast_solver_calls:                 1127
% 2.32/1.00  smt_solver_calls:                       0
% 2.32/1.00  smt_fast_solver_calls:                  0
% 2.32/1.00  prop_num_of_clauses:                    1297
% 2.32/1.00  prop_preprocess_simplified:             5340
% 2.32/1.00  prop_fo_subsumed:                       29
% 2.32/1.00  prop_solver_time:                       0.
% 2.32/1.00  smt_solver_time:                        0.
% 2.32/1.00  smt_fast_solver_time:                   0.
% 2.32/1.00  prop_fast_solver_time:                  0.
% 2.32/1.00  prop_unsat_core_time:                   0.
% 2.32/1.00  
% 2.32/1.00  ------ QBF
% 2.32/1.00  
% 2.32/1.00  qbf_q_res:                              0
% 2.32/1.00  qbf_num_tautologies:                    0
% 2.32/1.00  qbf_prep_cycles:                        0
% 2.32/1.00  
% 2.32/1.00  ------ BMC1
% 2.32/1.00  
% 2.32/1.00  bmc1_current_bound:                     -1
% 2.32/1.00  bmc1_last_solved_bound:                 -1
% 2.32/1.00  bmc1_unsat_core_size:                   -1
% 2.32/1.00  bmc1_unsat_core_parents_size:           -1
% 2.32/1.00  bmc1_merge_next_fun:                    0
% 2.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation
% 2.32/1.00  
% 2.32/1.00  inst_num_of_clauses:                    397
% 2.32/1.00  inst_num_in_passive:                    154
% 2.32/1.00  inst_num_in_active:                     193
% 2.32/1.00  inst_num_in_unprocessed:                50
% 2.32/1.00  inst_num_of_loops:                      260
% 2.32/1.00  inst_num_of_learning_restarts:          0
% 2.32/1.00  inst_num_moves_active_passive:          64
% 2.32/1.00  inst_lit_activity:                      0
% 2.32/1.00  inst_lit_activity_moves:                0
% 2.32/1.00  inst_num_tautologies:                   0
% 2.32/1.00  inst_num_prop_implied:                  0
% 2.32/1.00  inst_num_existing_simplified:           0
% 2.32/1.00  inst_num_eq_res_simplified:             0
% 2.32/1.00  inst_num_child_elim:                    0
% 2.32/1.00  inst_num_of_dismatching_blockings:      46
% 2.32/1.00  inst_num_of_non_proper_insts:           243
% 2.32/1.00  inst_num_of_duplicates:                 0
% 2.32/1.00  inst_inst_num_from_inst_to_res:         0
% 2.32/1.00  inst_dismatching_checking_time:         0.
% 2.32/1.00  
% 2.32/1.00  ------ Resolution
% 2.32/1.00  
% 2.32/1.00  res_num_of_clauses:                     0
% 2.32/1.00  res_num_in_passive:                     0
% 2.32/1.00  res_num_in_active:                      0
% 2.32/1.00  res_num_of_loops:                       147
% 2.32/1.00  res_forward_subset_subsumed:            19
% 2.32/1.00  res_backward_subset_subsumed:           0
% 2.32/1.00  res_forward_subsumed:                   0
% 2.32/1.00  res_backward_subsumed:                  0
% 2.32/1.00  res_forward_subsumption_resolution:     1
% 2.32/1.00  res_backward_subsumption_resolution:    0
% 2.32/1.00  res_clause_to_clause_subsumption:       220
% 2.32/1.00  res_orphan_elimination:                 0
% 2.32/1.00  res_tautology_del:                      31
% 2.32/1.00  res_num_eq_res_simplified:              0
% 2.32/1.00  res_num_sel_changes:                    0
% 2.32/1.00  res_moves_from_active_to_pass:          0
% 2.32/1.00  
% 2.32/1.00  ------ Superposition
% 2.32/1.00  
% 2.32/1.00  sup_time_total:                         0.
% 2.32/1.00  sup_time_generating:                    0.
% 2.32/1.00  sup_time_sim_full:                      0.
% 2.32/1.00  sup_time_sim_immed:                     0.
% 2.32/1.00  
% 2.32/1.00  sup_num_of_clauses:                     65
% 2.32/1.00  sup_num_in_active:                      50
% 2.32/1.00  sup_num_in_passive:                     15
% 2.32/1.00  sup_num_of_loops:                       51
% 2.32/1.00  sup_fw_superposition:                   37
% 2.32/1.00  sup_bw_superposition:                   13
% 2.32/1.00  sup_immediate_simplified:               8
% 2.32/1.00  sup_given_eliminated:                   0
% 2.32/1.00  comparisons_done:                       0
% 2.32/1.00  comparisons_avoided:                    15
% 2.32/1.00  
% 2.32/1.00  ------ Simplifications
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  sim_fw_subset_subsumed:                 5
% 2.32/1.00  sim_bw_subset_subsumed:                 1
% 2.32/1.00  sim_fw_subsumed:                        5
% 2.32/1.00  sim_bw_subsumed:                        0
% 2.32/1.00  sim_fw_subsumption_res:                 0
% 2.32/1.00  sim_bw_subsumption_res:                 0
% 2.32/1.00  sim_tautology_del:                      2
% 2.32/1.00  sim_eq_tautology_del:                   1
% 2.32/1.00  sim_eq_res_simp:                        0
% 2.32/1.00  sim_fw_demodulated:                     2
% 2.32/1.00  sim_bw_demodulated:                     1
% 2.32/1.00  sim_light_normalised:                   2
% 2.32/1.00  sim_joinable_taut:                      0
% 2.32/1.00  sim_joinable_simp:                      0
% 2.32/1.00  sim_ac_normalised:                      0
% 2.32/1.00  sim_smt_subsumption:                    0
% 2.32/1.00  
%------------------------------------------------------------------------------
