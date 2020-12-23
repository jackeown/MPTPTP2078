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
% DateTime   : Thu Dec  3 12:08:52 EST 2020

% Result     : Theorem 15.44s
% Output     : CNFRefutation 15.44s
% Verified   : 
% Statistics : Number of formulae       :  195 (2046 expanded)
%              Number of clauses        :  112 ( 338 expanded)
%              Number of leaves         :   23 ( 619 expanded)
%              Depth                    :   27
%              Number of atoms          :  700 (6988 expanded)
%              Number of equality atoms :  306 (2300 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f77])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK5) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK5,X0,k1_tarski(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
          & v1_funct_2(X3,sK2,k1_tarski(sK3))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k1_tarski(sK5) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f42,f41])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f64,f78,f78])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    k1_tarski(sK5) != k5_partfun1(sK2,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    k2_enumset1(sK5,sK5,sK5,sK5) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f76,f78,f78])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f94,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f95,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f94])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f61,f77,f77,f78])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_624,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_625,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3384,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(X1,X1,X1,X2)
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | sK1(k2_enumset1(X1,X1,X1,X2),X0) = X1
    | sK1(k2_enumset1(X1,X1,X1,X2),X0) = X2 ),
    inference(superposition,[status(thm)],[c_624,c_625])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_611,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3112,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_617])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3760,plain,
    ( r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3112,c_30])).

cnf(c_3761,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3760])).

cnf(c_30992,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),X0) = sK3
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
    | r2_hidden(X1,k5_partfun1(sK2,k2_enumset1(X0,X0,X0,X0),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3384,c_3761])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_10104,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r1_partfun1(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_20,c_25])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_614,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_621,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7826,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_621])).

cnf(c_7895,plain,
    ( r1_partfun1(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7826])).

cnf(c_10430,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10104,c_27,c_26,c_7895])).

cnf(c_10431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(renaming,[status(thm)],[c_10430])).

cnf(c_10622,plain,
    ( r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_10431,c_28])).

cnf(c_10756,plain,
    ( r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10622,c_29])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2155,plain,
    ( r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_9,c_24])).

cnf(c_3649,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_23,c_2155])).

cnf(c_3777,plain,
    ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3649,c_29,c_28])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3800,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | r2_hidden(X1,k1_xboole_0)
    | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_3777,c_215])).

cnf(c_10777,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | X0 != sK5
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_10756,c_3800])).

cnf(c_214,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_213,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1764,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_214,c_213])).

cnf(c_3796,plain,
    ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3777,c_1764])).

cnf(c_216,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3982,plain,
    ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3796,c_216])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4733,plain,
    ( v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3982,c_1])).

cnf(c_4734,plain,
    ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10772,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_10756,c_0])).

cnf(c_11333,plain,
    ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10777,c_1,c_3982,c_10772])).

cnf(c_5096,plain,
    ( m1_subset_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_21,c_2155])).

cnf(c_6145,plain,
    ( m1_subset_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_29,c_28])).

cnf(c_10116,plain,
    ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r1_partfun1(X0,sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_20,c_6145])).

cnf(c_11347,plain,
    ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r1_partfun1(X0,sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11333,c_10116])).

cnf(c_1062,plain,
    ( X0 != X1
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != X1
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1451,plain,
    ( X0 != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = X0
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1453,plain,
    ( k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k1_xboole_0
    | k1_xboole_0 != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1452,plain,
    ( k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_1789,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1791,plain,
    ( v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1789])).

cnf(c_18,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27859,plain,
    ( ~ r1_partfun1(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | sK5 = X0 ),
    inference(resolution,[status(thm)],[c_18,c_25])).

cnf(c_620,plain,
    ( X0 = X1
    | r1_partfun1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5997,plain,
    ( sK5 = X0
    | r1_partfun1(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | v1_partfun1(X0,sK2) != iProver_top
    | v1_partfun1(sK5,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_620])).

cnf(c_32,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_960,plain,
    ( r1_partfun1(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1733,plain,
    ( r1_partfun1(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1734,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_6618,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_partfun1(sK5,sK2) != iProver_top
    | v1_partfun1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | sK5 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5997,c_32,c_34,c_1734])).

cnf(c_6619,plain,
    ( sK5 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | v1_partfun1(X0,sK2) != iProver_top
    | v1_partfun1(sK5,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6618])).

cnf(c_6620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(X0)
    | sK5 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6619])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4877,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_16,c_25])).

cnf(c_5149,plain,
    ( v1_partfun1(sK5,sK2)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4877,c_27,c_26])).

cnf(c_5342,plain,
    ( v1_partfun1(sK5,sK2)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5149,c_1764])).

cnf(c_5566,plain,
    ( v1_partfun1(sK5,sK2)
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5342,c_216])).

cnf(c_8087,plain,
    ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_partfun1(sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5566,c_1])).

cnf(c_8088,plain,
    ( v1_partfun1(sK5,sK2)
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(renaming,[status(thm)],[c_8087])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1195,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[status(thm)],[c_0,c_5])).

cnf(c_8093,plain,
    ( v1_partfun1(sK5,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8088,c_1195])).

cnf(c_28206,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_partfun1(X0,sK2)
    | sK5 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27859,c_6620,c_8093])).

cnf(c_28207,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_funct_1(X0)
    | sK5 = X0 ),
    inference(renaming,[status(thm)],[c_28206])).

cnf(c_28370,plain,
    ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | sK5 = sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_28207,c_6145])).

cnf(c_29300,plain,
    ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | sK5 = sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28370,c_3777])).

cnf(c_30011,plain,
    ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5) = sK5
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_29300,c_1764])).

cnf(c_8,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3619,plain,
    ( sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5) != sK5
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_8,c_24])).

cnf(c_40079,plain,
    ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30011,c_3619])).

cnf(c_6281,plain,
    ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_6145,c_16])).

cnf(c_11349,plain,
    ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11333,c_6281])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3665,plain,
    ( v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_22,c_2155])).

cnf(c_3959,plain,
    ( v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_29,c_28])).

cnf(c_26671,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11349,c_1,c_1453,c_1452,c_1791,c_3959,c_10772])).

cnf(c_26672,plain,
    ( v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(renaming,[status(thm)],[c_26671])).

cnf(c_40095,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_40079,c_26672])).

cnf(c_53353,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11347,c_1,c_1453,c_1452,c_1791,c_10772,c_40095])).

cnf(c_53362,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53353,c_1764])).

cnf(c_53598,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30992,c_53362])).

cnf(c_13,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_627,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1745,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_632])).

cnf(c_1796,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1745])).

cnf(c_1802,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1796])).

cnf(c_2565,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k2_enumset1(X4,X4,X4,X4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1802])).

cnf(c_54394,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53598,c_2565])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_54443,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54394,c_10])).

cnf(c_79,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54443,c_79])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n023.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:39:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.44/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.44/2.48  
% 15.44/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.44/2.48  
% 15.44/2.48  ------  iProver source info
% 15.44/2.48  
% 15.44/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.44/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.44/2.48  git: non_committed_changes: false
% 15.44/2.48  git: last_make_outside_of_git: false
% 15.44/2.48  
% 15.44/2.48  ------ 
% 15.44/2.48  ------ Parsing...
% 15.44/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.44/2.48  
% 15.44/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.44/2.48  
% 15.44/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.44/2.48  
% 15.44/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.44/2.48  ------ Proving...
% 15.44/2.48  ------ Problem Properties 
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  clauses                                 30
% 15.44/2.48  conjectures                             6
% 15.44/2.48  EPR                                     4
% 15.44/2.48  Horn                                    23
% 15.44/2.48  unary                                   13
% 15.44/2.48  binary                                  1
% 15.44/2.48  lits                                    86
% 15.44/2.48  lits eq                                 25
% 15.44/2.48  fd_pure                                 0
% 15.44/2.48  fd_pseudo                               0
% 15.44/2.48  fd_cond                                 3
% 15.44/2.48  fd_pseudo_cond                          6
% 15.44/2.48  AC symbols                              0
% 15.44/2.48  
% 15.44/2.48  ------ Input Options Time Limit: Unbounded
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  ------ 
% 15.44/2.48  Current options:
% 15.44/2.48  ------ 
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  ------ Proving...
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  % SZS status Theorem for theBenchmark.p
% 15.44/2.48  
% 15.44/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.44/2.48  
% 15.44/2.48  fof(f7,axiom,(
% 15.44/2.48    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f19,plain,(
% 15.44/2.48    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.44/2.48    inference(ennf_transformation,[],[f7])).
% 15.44/2.48  
% 15.44/2.48  fof(f37,plain,(
% 15.44/2.48    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 15.44/2.48    introduced(choice_axiom,[])).
% 15.44/2.48  
% 15.44/2.48  fof(f38,plain,(
% 15.44/2.48    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.44/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f37])).
% 15.44/2.48  
% 15.44/2.48  fof(f55,plain,(
% 15.44/2.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.44/2.48    inference(cnf_transformation,[],[f38])).
% 15.44/2.48  
% 15.44/2.48  fof(f4,axiom,(
% 15.44/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f52,plain,(
% 15.44/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f4])).
% 15.44/2.48  
% 15.44/2.48  fof(f5,axiom,(
% 15.44/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f53,plain,(
% 15.44/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f5])).
% 15.44/2.48  
% 15.44/2.48  fof(f6,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f54,plain,(
% 15.44/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f6])).
% 15.44/2.48  
% 15.44/2.48  fof(f77,plain,(
% 15.44/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.44/2.48    inference(definition_unfolding,[],[f53,f54])).
% 15.44/2.48  
% 15.44/2.48  fof(f78,plain,(
% 15.44/2.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.44/2.48    inference(definition_unfolding,[],[f52,f77])).
% 15.44/2.48  
% 15.44/2.48  fof(f86,plain,(
% 15.44/2.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 15.44/2.48    inference(definition_unfolding,[],[f55,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f3,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f32,plain,(
% 15.44/2.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 15.44/2.48    inference(nnf_transformation,[],[f3])).
% 15.44/2.48  
% 15.44/2.48  fof(f33,plain,(
% 15.44/2.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 15.44/2.48    inference(flattening,[],[f32])).
% 15.44/2.48  
% 15.44/2.48  fof(f34,plain,(
% 15.44/2.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 15.44/2.48    inference(rectify,[],[f33])).
% 15.44/2.48  
% 15.44/2.48  fof(f35,plain,(
% 15.44/2.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.44/2.48    introduced(choice_axiom,[])).
% 15.44/2.48  
% 15.44/2.48  fof(f36,plain,(
% 15.44/2.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 15.44/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 15.44/2.48  
% 15.44/2.48  fof(f46,plain,(
% 15.44/2.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 15.44/2.48    inference(cnf_transformation,[],[f36])).
% 15.44/2.48  
% 15.44/2.48  fof(f84,plain,(
% 15.44/2.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 15.44/2.48    inference(definition_unfolding,[],[f46,f77])).
% 15.44/2.48  
% 15.44/2.48  fof(f98,plain,(
% 15.44/2.48    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 15.44/2.48    inference(equality_resolution,[],[f84])).
% 15.44/2.48  
% 15.44/2.48  fof(f15,conjecture,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f16,negated_conjecture,(
% 15.44/2.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 15.44/2.48    inference(negated_conjecture,[],[f15])).
% 15.44/2.48  
% 15.44/2.48  fof(f30,plain,(
% 15.44/2.48    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f16])).
% 15.44/2.48  
% 15.44/2.48  fof(f31,plain,(
% 15.44/2.48    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f30])).
% 15.44/2.48  
% 15.44/2.48  fof(f42,plain,(
% 15.44/2.48    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK5) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK5,X0,k1_tarski(X1)) & v1_funct_1(sK5))) )),
% 15.44/2.48    introduced(choice_axiom,[])).
% 15.44/2.48  
% 15.44/2.48  fof(f41,plain,(
% 15.44/2.48    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(X3,sK2,k1_tarski(sK3)) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4))),
% 15.44/2.48    introduced(choice_axiom,[])).
% 15.44/2.48  
% 15.44/2.48  fof(f43,plain,(
% 15.44/2.48    (k1_tarski(sK5) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4)),
% 15.44/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f42,f41])).
% 15.44/2.48  
% 15.44/2.48  fof(f72,plain,(
% 15.44/2.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f93,plain,(
% 15.44/2.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 15.44/2.48    inference(definition_unfolding,[],[f72,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f14,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f28,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f14])).
% 15.44/2.48  
% 15.44/2.48  fof(f29,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f28])).
% 15.44/2.48  
% 15.44/2.48  fof(f70,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f29])).
% 15.44/2.48  
% 15.44/2.48  fof(f71,plain,(
% 15.44/2.48    v1_funct_1(sK4)),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f13,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f26,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f13])).
% 15.44/2.48  
% 15.44/2.48  fof(f27,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f26])).
% 15.44/2.48  
% 15.44/2.48  fof(f66,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f27])).
% 15.44/2.48  
% 15.44/2.48  fof(f75,plain,(
% 15.44/2.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f91,plain,(
% 15.44/2.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 15.44/2.48    inference(definition_unfolding,[],[f75,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f73,plain,(
% 15.44/2.48    v1_funct_1(sK5)),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f74,plain,(
% 15.44/2.48    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f92,plain,(
% 15.44/2.48    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 15.44/2.48    inference(definition_unfolding,[],[f74,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f11,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f22,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f11])).
% 15.44/2.48  
% 15.44/2.48  fof(f23,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f22])).
% 15.44/2.48  
% 15.44/2.48  fof(f64,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f23])).
% 15.44/2.48  
% 15.44/2.48  fof(f89,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(definition_unfolding,[],[f64,f78,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f68,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f29])).
% 15.44/2.48  
% 15.44/2.48  fof(f76,plain,(
% 15.44/2.48    k1_tarski(sK5) != k5_partfun1(sK2,k1_tarski(sK3),sK4)),
% 15.44/2.48    inference(cnf_transformation,[],[f43])).
% 15.44/2.48  
% 15.44/2.48  fof(f90,plain,(
% 15.44/2.48    k2_enumset1(sK5,sK5,sK5,sK5) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 15.44/2.48    inference(definition_unfolding,[],[f76,f78,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f2,axiom,(
% 15.44/2.48    v1_xboole_0(k1_xboole_0)),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f45,plain,(
% 15.44/2.48    v1_xboole_0(k1_xboole_0)),
% 15.44/2.48    inference(cnf_transformation,[],[f2])).
% 15.44/2.48  
% 15.44/2.48  fof(f1,axiom,(
% 15.44/2.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f17,plain,(
% 15.44/2.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 15.44/2.48    inference(unused_predicate_definition_removal,[],[f1])).
% 15.44/2.48  
% 15.44/2.48  fof(f18,plain,(
% 15.44/2.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 15.44/2.48    inference(ennf_transformation,[],[f17])).
% 15.44/2.48  
% 15.44/2.48  fof(f44,plain,(
% 15.44/2.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f18])).
% 15.44/2.48  
% 15.44/2.48  fof(f12,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f24,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f12])).
% 15.44/2.48  
% 15.44/2.48  fof(f25,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f24])).
% 15.44/2.48  
% 15.44/2.48  fof(f65,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f25])).
% 15.44/2.48  
% 15.44/2.48  fof(f10,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f20,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.44/2.48    inference(ennf_transformation,[],[f10])).
% 15.44/2.48  
% 15.44/2.48  fof(f21,plain,(
% 15.44/2.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.44/2.48    inference(flattening,[],[f20])).
% 15.44/2.48  
% 15.44/2.48  fof(f62,plain,(
% 15.44/2.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f21])).
% 15.44/2.48  
% 15.44/2.48  fof(f48,plain,(
% 15.44/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 15.44/2.48    inference(cnf_transformation,[],[f36])).
% 15.44/2.48  
% 15.44/2.48  fof(f82,plain,(
% 15.44/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 15.44/2.48    inference(definition_unfolding,[],[f48,f77])).
% 15.44/2.48  
% 15.44/2.48  fof(f94,plain,(
% 15.44/2.48    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 15.44/2.48    inference(equality_resolution,[],[f82])).
% 15.44/2.48  
% 15.44/2.48  fof(f95,plain,(
% 15.44/2.48    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 15.44/2.48    inference(equality_resolution,[],[f94])).
% 15.44/2.48  
% 15.44/2.48  fof(f56,plain,(
% 15.44/2.48    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.44/2.48    inference(cnf_transformation,[],[f38])).
% 15.44/2.48  
% 15.44/2.48  fof(f85,plain,(
% 15.44/2.48    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 15.44/2.48    inference(definition_unfolding,[],[f56,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f69,plain,(
% 15.44/2.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.44/2.48    inference(cnf_transformation,[],[f29])).
% 15.44/2.48  
% 15.44/2.48  fof(f9,axiom,(
% 15.44/2.48    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f61,plain,(
% 15.44/2.48    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 15.44/2.48    inference(cnf_transformation,[],[f9])).
% 15.44/2.48  
% 15.44/2.48  fof(f87,plain,(
% 15.44/2.48    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 15.44/2.48    inference(definition_unfolding,[],[f61,f77,f77,f78])).
% 15.44/2.48  
% 15.44/2.48  fof(f8,axiom,(
% 15.44/2.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.44/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.44/2.48  
% 15.44/2.48  fof(f39,plain,(
% 15.44/2.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.44/2.48    inference(nnf_transformation,[],[f8])).
% 15.44/2.48  
% 15.44/2.48  fof(f40,plain,(
% 15.44/2.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.44/2.48    inference(flattening,[],[f39])).
% 15.44/2.48  
% 15.44/2.48  fof(f59,plain,(
% 15.44/2.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.44/2.48    inference(cnf_transformation,[],[f40])).
% 15.44/2.48  
% 15.44/2.48  fof(f99,plain,(
% 15.44/2.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.44/2.48    inference(equality_resolution,[],[f59])).
% 15.44/2.48  
% 15.44/2.48  cnf(c_9,plain,
% 15.44/2.48      ( r2_hidden(sK1(X0,X1),X0)
% 15.44/2.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 15.44/2.48      | k1_xboole_0 = X0 ),
% 15.44/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_624,plain,
% 15.44/2.48      ( k2_enumset1(X0,X0,X0,X0) = X1
% 15.44/2.48      | k1_xboole_0 = X1
% 15.44/2.48      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_7,plain,
% 15.44/2.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 15.44/2.48      inference(cnf_transformation,[],[f98]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_625,plain,
% 15.44/2.48      ( X0 = X1
% 15.44/2.48      | X0 = X2
% 15.44/2.48      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3384,plain,
% 15.44/2.48      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(X1,X1,X1,X2)
% 15.44/2.48      | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
% 15.44/2.48      | sK1(k2_enumset1(X1,X1,X1,X2),X0) = X1
% 15.44/2.48      | sK1(k2_enumset1(X1,X1,X1,X2),X0) = X2 ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_624,c_625]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_28,negated_conjecture,
% 15.44/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 15.44/2.48      inference(cnf_transformation,[],[f93]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_611,plain,
% 15.44/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_21,plain,
% 15.44/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 15.44/2.48      | ~ v1_funct_1(X0) ),
% 15.44/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_617,plain,
% 15.44/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.44/2.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.44/2.48      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3112,plain,
% 15.44/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
% 15.44/2.48      | r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 15.44/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_611,c_617]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_29,negated_conjecture,
% 15.44/2.48      ( v1_funct_1(sK4) ),
% 15.44/2.48      inference(cnf_transformation,[],[f71]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_30,plain,
% 15.44/2.48      ( v1_funct_1(sK4) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3760,plain,
% 15.44/2.48      ( r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_3112,c_30]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3761,plain,
% 15.44/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
% 15.44/2.48      | r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_3760]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_30992,plain,
% 15.44/2.48      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 15.44/2.48      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),X0) = sK3
% 15.44/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top
% 15.44/2.48      | r2_hidden(X1,k5_partfun1(sK2,k2_enumset1(X0,X0,X0,X0),sK4)) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_3384,c_3761]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_20,plain,
% 15.44/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.44/2.48      | ~ r1_partfun1(X3,X0)
% 15.44/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 15.44/2.48      | ~ v1_funct_1(X3)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | k1_xboole_0 = X2 ),
% 15.44/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_25,negated_conjecture,
% 15.44/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 15.44/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10104,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | ~ r1_partfun1(X0,sK5)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK5)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_20,c_25]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_27,negated_conjecture,
% 15.44/2.48      ( v1_funct_1(sK5) ),
% 15.44/2.48      inference(cnf_transformation,[],[f73]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_26,negated_conjecture,
% 15.44/2.48      ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 15.44/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_614,plain,
% 15.44/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_17,plain,
% 15.44/2.48      ( r1_partfun1(X0,X1)
% 15.44/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(X1) ),
% 15.44/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_621,plain,
% 15.44/2.48      ( r1_partfun1(X0,X1) = iProver_top
% 15.44/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top
% 15.44/2.48      | v1_funct_1(X1) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_7826,plain,
% 15.44/2.48      ( r1_partfun1(X0,sK5) = iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top
% 15.44/2.48      | v1_funct_1(sK5) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_614,c_621]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_7895,plain,
% 15.44/2.48      ( r1_partfun1(X0,sK5)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK5) ),
% 15.44/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_7826]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10430,plain,
% 15.44/2.48      ( ~ v1_funct_1(X0)
% 15.44/2.48      | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_10104,c_27,c_26,c_7895]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10431,plain,
% 15.44/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_10430]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10622,plain,
% 15.44/2.48      ( r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | ~ v1_funct_1(sK4)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_10431,c_28]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10756,plain,
% 15.44/2.48      ( r2_hidden(sK5,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_10622,c_29]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_23,plain,
% 15.44/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | v1_funct_1(X3) ),
% 15.44/2.48      inference(cnf_transformation,[],[f68]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_24,negated_conjecture,
% 15.44/2.48      ( k2_enumset1(sK5,sK5,sK5,sK5) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_2155,plain,
% 15.44/2.48      ( r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_9,c_24]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3649,plain,
% 15.44/2.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | ~ v1_funct_1(sK4)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_23,c_2155]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3777,plain,
% 15.44/2.48      ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_3649,c_29,c_28]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_215,plain,
% 15.44/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.44/2.48      theory(equality) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3800,plain,
% 15.44/2.48      ( ~ r2_hidden(X0,k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | r2_hidden(X1,k1_xboole_0)
% 15.44/2.48      | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | X1 != X0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_3777,c_215]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10777,plain,
% 15.44/2.48      ( r2_hidden(X0,k1_xboole_0)
% 15.44/2.48      | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | X0 != sK5
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_10756,c_3800]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_214,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_213,plain,( X0 = X0 ),theory(equality) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1764,plain,
% 15.44/2.48      ( X0 != X1 | X1 = X0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_214,c_213]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3796,plain,
% 15.44/2.48      ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k1_xboole_0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_3777,c_1764]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_216,plain,
% 15.44/2.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.44/2.48      theory(equality) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3982,plain,
% 15.44/2.48      ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_3796,c_216]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1,plain,
% 15.44/2.48      ( v1_xboole_0(k1_xboole_0) ),
% 15.44/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_4733,plain,
% 15.44/2.48      ( v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_3982,c_1]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_4734,plain,
% 15.44/2.48      ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_4733]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_0,plain,
% 15.44/2.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.44/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10772,plain,
% 15.44/2.48      ( ~ v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_10756,c_0]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_11333,plain,
% 15.44/2.48      ( v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_10777,c_1,c_3982,c_10772]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5096,plain,
% 15.44/2.48      ( m1_subset_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_funct_1(sK4)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_21,c_2155]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_6145,plain,
% 15.44/2.48      ( m1_subset_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_5096,c_29,c_28]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10116,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | ~ r1_partfun1(X0,sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_20,c_6145]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_11347,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | ~ r1_partfun1(X0,sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | r2_hidden(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),X0))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(backward_subsumption_resolution,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_11333,c_10116]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1062,plain,
% 15.44/2.48      ( X0 != X1
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != X1
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = X0 ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_214]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1451,plain,
% 15.44/2.48      ( X0 != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = X0
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_1062]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1453,plain,
% 15.44/2.48      ( k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k1_xboole_0
% 15.44/2.48      | k1_xboole_0 != k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_1451]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1452,plain,
% 15.44/2.48      ( k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_213]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1789,plain,
% 15.44/2.48      ( ~ v1_xboole_0(X0)
% 15.44/2.48      | v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != X0 ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_216]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1791,plain,
% 15.44/2.48      ( v1_xboole_0(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 15.44/2.48      | ~ v1_xboole_0(k1_xboole_0)
% 15.44/2.48      | k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k1_xboole_0 ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_1789]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_18,plain,
% 15.44/2.48      ( ~ r1_partfun1(X0,X1)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.44/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.44/2.48      | ~ v1_partfun1(X1,X2)
% 15.44/2.48      | ~ v1_partfun1(X0,X2)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(X1)
% 15.44/2.48      | X1 = X0 ),
% 15.44/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_27859,plain,
% 15.44/2.48      ( ~ r1_partfun1(X0,sK5)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_partfun1(X0,sK2)
% 15.44/2.48      | ~ v1_partfun1(sK5,sK2)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK5)
% 15.44/2.48      | sK5 = X0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_18,c_25]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_620,plain,
% 15.44/2.48      ( X0 = X1
% 15.44/2.48      | r1_partfun1(X1,X0) != iProver_top
% 15.44/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.44/2.48      | v1_partfun1(X0,X2) != iProver_top
% 15.44/2.48      | v1_partfun1(X1,X2) != iProver_top
% 15.44/2.48      | v1_funct_1(X1) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5997,plain,
% 15.44/2.48      ( sK5 = X0
% 15.44/2.48      | r1_partfun1(X0,sK5) != iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | v1_partfun1(X0,sK2) != iProver_top
% 15.44/2.48      | v1_partfun1(sK5,sK2) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top
% 15.44/2.48      | v1_funct_1(sK5) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_614,c_620]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_32,plain,
% 15.44/2.48      ( v1_funct_1(sK5) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_34,plain,
% 15.44/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_960,plain,
% 15.44/2.48      ( r1_partfun1(X0,sK5)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 15.44/2.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK5) ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_17]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1733,plain,
% 15.44/2.48      ( r1_partfun1(X0,sK5)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | ~ v1_funct_1(sK5) ),
% 15.44/2.48      inference(instantiation,[status(thm)],[c_960]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1734,plain,
% 15.44/2.48      ( r1_partfun1(X0,sK5) = iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top
% 15.44/2.48      | v1_funct_1(sK5) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_6618,plain,
% 15.44/2.48      ( v1_funct_1(X0) != iProver_top
% 15.44/2.48      | v1_partfun1(sK5,sK2) != iProver_top
% 15.44/2.48      | v1_partfun1(X0,sK2) != iProver_top
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | sK5 = X0 ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_5997,c_32,c_34,c_1734]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_6619,plain,
% 15.44/2.48      ( sK5 = X0
% 15.44/2.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 15.44/2.48      | v1_partfun1(X0,sK2) != iProver_top
% 15.44/2.48      | v1_partfun1(sK5,sK2) != iProver_top
% 15.44/2.48      | v1_funct_1(X0) != iProver_top ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_6618]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_6620,plain,
% 15.44/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_partfun1(X0,sK2)
% 15.44/2.48      | ~ v1_partfun1(sK5,sK2)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | sK5 = X0 ),
% 15.44/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_6619]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_16,plain,
% 15.44/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | v1_partfun1(X0,X1)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | k1_xboole_0 = X2 ),
% 15.44/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_4877,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | v1_partfun1(sK5,sK2)
% 15.44/2.48      | ~ v1_funct_1(sK5)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_16,c_25]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5149,plain,
% 15.44/2.48      ( v1_partfun1(sK5,sK2)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_4877,c_27,c_26]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5342,plain,
% 15.44/2.48      ( v1_partfun1(sK5,sK2)
% 15.44/2.48      | k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_5149,c_1764]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5566,plain,
% 15.44/2.48      ( v1_partfun1(sK5,sK2)
% 15.44/2.48      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_5342,c_216]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_8087,plain,
% 15.44/2.48      ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | v1_partfun1(sK5,sK2) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_5566,c_1]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_8088,plain,
% 15.44/2.48      ( v1_partfun1(sK5,sK2)
% 15.44/2.48      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_8087]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_5,plain,
% 15.44/2.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 15.44/2.48      inference(cnf_transformation,[],[f95]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1195,plain,
% 15.44/2.48      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_0,c_5]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_8093,plain,
% 15.44/2.48      ( v1_partfun1(sK5,sK2) ),
% 15.44/2.48      inference(forward_subsumption_resolution,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_8088,c_1195]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_28206,plain,
% 15.44/2.48      ( ~ v1_funct_1(X0)
% 15.44/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_partfun1(X0,sK2)
% 15.44/2.48      | sK5 = X0 ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_27859,c_6620,c_8093]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_28207,plain,
% 15.44/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_partfun1(X0,sK2)
% 15.44/2.48      | ~ v1_funct_1(X0)
% 15.44/2.48      | sK5 = X0 ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_28206]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_28370,plain,
% 15.44/2.48      ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | sK5 = sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_28207,c_6145]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_29300,plain,
% 15.44/2.48      ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | sK5 = sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_28370,c_3777]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_30011,plain,
% 15.44/2.48      ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5) = sK5
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_29300,c_1764]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_8,plain,
% 15.44/2.48      ( k2_enumset1(X0,X0,X0,X0) = X1
% 15.44/2.48      | sK1(X1,X0) != X0
% 15.44/2.48      | k1_xboole_0 = X1 ),
% 15.44/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3619,plain,
% 15.44/2.48      ( sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5) != sK5
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_8,c_24]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_40079,plain,
% 15.44/2.48      ( ~ v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_30011,c_3619]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_6281,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | ~ v1_funct_1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5))
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_6145,c_16]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_11349,plain,
% 15.44/2.48      ( ~ v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(backward_subsumption_resolution,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_11333,c_6281]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_22,plain,
% 15.44/2.48      ( v1_funct_2(X0,X1,X2)
% 15.44/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.44/2.48      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 15.44/2.48      | ~ v1_funct_1(X3) ),
% 15.44/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3665,plain,
% 15.44/2.48      ( v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 15.44/2.48      | ~ v1_funct_1(sK4)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_22,c_2155]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_3959,plain,
% 15.44/2.48      ( v1_funct_2(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_3665,c_29,c_28]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_26671,plain,
% 15.44/2.48      ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_11349,c_1,c_1453,c_1452,c_1791,c_3959,c_10772]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_26672,plain,
% 15.44/2.48      ( v1_partfun1(sK1(k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK5),sK2)
% 15.44/2.48      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(renaming,[status(thm)],[c_26671]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_40095,plain,
% 15.44/2.48      ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
% 15.44/2.48      | k1_xboole_0 = k5_partfun1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_40079,c_26672]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_53353,plain,
% 15.44/2.48      ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_11347,c_1,c_1453,c_1452,c_1791,c_10772,c_40095]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_53362,plain,
% 15.44/2.48      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 15.44/2.48      inference(resolution,[status(thm)],[c_53353,c_1764]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_53598,plain,
% 15.44/2.48      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 15.44/2.48      inference(global_propositional_subsumption,
% 15.44/2.48                [status(thm)],
% 15.44/2.48                [c_30992,c_53362]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_13,plain,
% 15.44/2.48      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 15.44/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_627,plain,
% 15.44/2.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_632,plain,
% 15.44/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.44/2.48      | v1_xboole_0(X1) != iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1745,plain,
% 15.44/2.48      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_627,c_632]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1796,plain,
% 15.44/2.48      ( v1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_13,c_1745]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_1802,plain,
% 15.44/2.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3))) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_13,c_1796]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_2565,plain,
% 15.44/2.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k2_enumset1(X4,X4,X4,X4))) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_13,c_1802]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_54394,plain,
% 15.44/2.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k1_xboole_0)) != iProver_top ),
% 15.44/2.48      inference(superposition,[status(thm)],[c_53598,c_2565]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_10,plain,
% 15.44/2.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.44/2.48      inference(cnf_transformation,[],[f99]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_54443,plain,
% 15.44/2.48      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.44/2.48      inference(demodulation,[status(thm)],[c_54394,c_10]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(c_79,plain,
% 15.44/2.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.44/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.44/2.48  
% 15.44/2.48  cnf(contradiction,plain,
% 15.44/2.48      ( $false ),
% 15.44/2.48      inference(minisat,[status(thm)],[c_54443,c_79]) ).
% 15.44/2.48  
% 15.44/2.48  
% 15.44/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.44/2.48  
% 15.44/2.48  ------                               Statistics
% 15.44/2.48  
% 15.44/2.48  ------ Selected
% 15.44/2.48  
% 15.44/2.48  total_time:                             1.636
% 15.44/2.48  
%------------------------------------------------------------------------------
