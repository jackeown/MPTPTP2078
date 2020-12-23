%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:52 EST 2020

% Result     : Theorem 11.91s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :  248 (14926 expanded)
%              Number of clauses        :  164 (3178 expanded)
%              Number of leaves         :   24 (4137 expanded)
%              Depth                    :   34
%              Number of atoms          :  844 (51858 expanded)
%              Number of equality atoms :  464 (18231 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK4) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK4,X0,k1_tarski(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK1,k1_tarski(sK2),sK3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
          & v1_funct_2(X3,sK1,k1_tarski(sK2))
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f41,f40])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f64,f78,f78])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

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
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f76,f78,f78])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f58,f77,f77,f78])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f78])).

cnf(c_1088,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2302,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_1088,c_0])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2304,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_1088,c_6])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2414,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2304,c_3])).

cnf(c_9919,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_zfmisc_1(X2,k1_xboole_0))
    | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1) ),
    inference(resolution,[status(thm)],[c_2302,c_2414])).

cnf(c_1087,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2759,plain,
    ( X0 != k1_xboole_0
    | k2_zfmisc_1(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_1087,c_6])).

cnf(c_1086,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2761,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1087,c_1086])).

cnf(c_3257,plain,
    ( X0 = k2_zfmisc_1(X1,k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2759,c_2761])).

cnf(c_3512,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3257,c_1088])).

cnf(c_1097,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_1090,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6352,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | r2_hidden(X4,k5_partfun1(X5,X6,X7))
    | X5 != X1
    | X4 != X0
    | X6 != X2
    | X7 != X3 ),
    inference(resolution,[status(thm)],[c_1097,c_1090])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7744,plain,
    ( ~ v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_21,c_26])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_525,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(X1,k5_partfun1(X2,X3,X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X3
    | sK1 != X2
    | sK4 != X1
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_526,plain,
    ( ~ r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_28,c_26])).

cnf(c_531,plain,
    ( ~ r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(renaming,[status(thm)],[c_530])).

cnf(c_1517,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1524,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7114,plain,
    ( r1_partfun1(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1524])).

cnf(c_7183,plain,
    ( r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7114])).

cnf(c_7853,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7744,c_28,c_26,c_526,c_7183])).

cnf(c_7854,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(renaming,[status(thm)],[c_7853])).

cnf(c_7879,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_7854,c_26])).

cnf(c_7884,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7879,c_28])).

cnf(c_32699,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | X2 != k2_enumset1(sK2,sK2,sK2,sK2)
    | X1 != sK1
    | X0 != sK4
    | X3 != sK4
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_6352,c_7884])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5067,plain,
    ( ~ v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | v1_partfun1(sK4,sK1)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_17,c_26])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_553,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | v1_partfun1(sK4,sK1)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_555,plain,
    ( v1_partfun1(sK4,sK1)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_28,c_26])).

cnf(c_5094,plain,
    ( v1_partfun1(sK4,sK1)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5067,c_28,c_26,c_553])).

cnf(c_5198,plain,
    ( v1_partfun1(sK4,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5094,c_2761])).

cnf(c_5388,plain,
    ( v1_partfun1(sK4,sK1)
    | X0 != k1_xboole_0
    | k2_enumset1(sK2,sK2,sK2,sK2) = X0 ),
    inference(resolution,[status(thm)],[c_5198,c_1087])).

cnf(c_5200,plain,
    ( v1_partfun1(sK4,sK1)
    | X0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_5094,c_1087])).

cnf(c_10617,plain,
    ( v1_partfun1(sK4,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_5388,c_5200])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_69,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_70,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3147,plain,
    ( X0 != X1
    | X0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_3148,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_13930,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10617,c_69,c_70,c_3148])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1530,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1514,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3417,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1520])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3972,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3417,c_31])).

cnf(c_3973,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3972])).

cnf(c_3980,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_3973])).

cnf(c_1521,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4437,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_1521])).

cnf(c_25,negated_conjecture,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1791,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4))
    | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1792,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_1895,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4))
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1896,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0
    | r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_1898,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k1_xboole_0
    | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2250,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2253,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1519,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2659,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1519])).

cnf(c_2974,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_31])).

cnf(c_2975,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2974])).

cnf(c_3464,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_2975])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1518,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2016,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1518])).

cnf(c_2401,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2016,c_31])).

cnf(c_2402,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2401])).

cnf(c_3465,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_2402])).

cnf(c_4434,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1521])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_34,plain,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1865,plain,
    ( r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2139,plain,
    ( r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_2140,plain,
    ( r1_partfun1(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2139])).

cnf(c_4991,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_33,c_34,c_35,c_2140])).

cnf(c_4992,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4991])).

cnf(c_5002,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_4992])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4350,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8884,plain,
    ( ~ r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_8885,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8884])).

cnf(c_7117,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_1524])).

cnf(c_10105,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7117,c_3465])).

cnf(c_10106,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10105])).

cnf(c_24189,plain,
    ( v1_funct_1(X1) != iProver_top
    | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4437,c_31,c_25,c_1792,c_1898,c_2253,c_3464,c_3465,c_5002,c_8885,c_10106])).

cnf(c_24190,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_24189])).

cnf(c_3416,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1520])).

cnf(c_3839,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3416,c_33])).

cnf(c_3840,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3839])).

cnf(c_24202,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24190,c_3840])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24205,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24190,c_3973])).

cnf(c_25139,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24202,c_31,c_25,c_1792,c_1898,c_2253,c_3980,c_5002,c_8885])).

cnf(c_19,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1523,plain,
    ( X0 = X1
    | r1_partfun1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5616,plain,
    ( sK4 = X0
    | r1_partfun1(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1523])).

cnf(c_6279,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5616,c_33,c_35,c_2140])).

cnf(c_6280,plain,
    ( sK4 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6279])).

cnf(c_25158,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25139,c_6280])).

cnf(c_5199,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_partfun1(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5198])).

cnf(c_2015,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1518])).

cnf(c_2268,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2015,c_33])).

cnf(c_2269,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2268])).

cnf(c_24204,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24190,c_2269])).

cnf(c_25033,plain,
    ( v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24204,c_33,c_35])).

cnf(c_25034,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_25033])).

cnf(c_2658,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1519])).

cnf(c_2965,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2658,c_33])).

cnf(c_2966,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2965])).

cnf(c_24203,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24190,c_2966])).

cnf(c_25129,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24203,c_31,c_25,c_1792,c_1898,c_2253,c_3464,c_5002,c_8885])).

cnf(c_1525,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25153,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25139,c_1525])).

cnf(c_26451,plain,
    ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25158,c_5199,c_25034,c_25129,c_25153])).

cnf(c_26452,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(renaming,[status(thm)],[c_26451])).

cnf(c_26512,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(superposition,[status(thm)],[c_26452,c_25])).

cnf(c_28473,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_26512])).

cnf(c_1940,plain,
    ( ~ r1_tarski(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2389,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2390,plain,
    ( r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1946,plain,
    ( X0 != X1
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X1
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_2458,plain,
    ( X0 != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2460,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k1_xboole_0 != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_4,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4836,plain,
    ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) != sK4
    | k1_xboole_0 = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[status(thm)],[c_4,c_25])).

cnf(c_28742,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28473,c_31,c_25,c_1792,c_1898,c_2253,c_2389,c_2390,c_2460,c_4836,c_5002,c_8885])).

cnf(c_32858,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32699,c_31,c_25,c_69,c_70,c_1792,c_1898,c_2253,c_2389,c_2390,c_2460,c_3148,c_4836,c_5002,c_8885,c_28473])).

cnf(c_32870,plain,
    ( X0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_32858,c_1087])).

cnf(c_11,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2701,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_11,c_9])).

cnf(c_3637,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3))) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_11,c_2701])).

cnf(c_9637,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k2_enumset1(X4,X4,X4,X4))) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_11,c_3637])).

cnf(c_29250,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_28742,c_9637])).

cnf(c_29354,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29250,c_6])).

cnf(c_29355,plain,
    ( k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_29354])).

cnf(c_33306,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32870,c_29355])).

cnf(c_33361,plain,
    ( X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33306,c_2761])).

cnf(c_44200,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9919,c_3512,c_33361])).

cnf(c_44206,plain,
    ( r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44200,c_2414])).

cnf(c_2284,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_0,c_25])).

cnf(c_44267,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_44206,c_2284])).

cnf(c_46729,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44267,c_44206])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.91/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.91/1.99  
% 11.91/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.91/1.99  
% 11.91/1.99  ------  iProver source info
% 11.91/1.99  
% 11.91/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.91/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.91/1.99  git: non_committed_changes: false
% 11.91/1.99  git: last_make_outside_of_git: false
% 11.91/1.99  
% 11.91/1.99  ------ 
% 11.91/1.99  ------ Parsing...
% 11.91/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.91/1.99  
% 11.91/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.91/1.99  
% 11.91/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.91/1.99  
% 11.91/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.91/1.99  ------ Proving...
% 11.91/1.99  ------ Problem Properties 
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  clauses                                 30
% 11.91/1.99  conjectures                             6
% 11.91/1.99  EPR                                     5
% 11.91/1.99  Horn                                    25
% 11.91/1.99  unary                                   12
% 11.91/1.99  binary                                  4
% 11.91/1.99  lits                                    84
% 11.91/1.99  lits eq                                 21
% 11.91/1.99  fd_pure                                 0
% 11.91/1.99  fd_pseudo                               0
% 11.91/1.99  fd_cond                                 5
% 11.91/1.99  fd_pseudo_cond                          4
% 11.91/1.99  AC symbols                              0
% 11.91/1.99  
% 11.91/1.99  ------ Input Options Time Limit: Unbounded
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  ------ 
% 11.91/1.99  Current options:
% 11.91/1.99  ------ 
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  ------ Proving...
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  % SZS status Theorem for theBenchmark.p
% 11.91/1.99  
% 11.91/1.99   Resolution empty clause
% 11.91/1.99  
% 11.91/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.91/1.99  
% 11.91/1.99  fof(f1,axiom,(
% 11.91/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f32,plain,(
% 11.91/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.91/1.99    inference(nnf_transformation,[],[f1])).
% 11.91/1.99  
% 11.91/1.99  fof(f33,plain,(
% 11.91/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.91/1.99    inference(flattening,[],[f32])).
% 11.91/1.99  
% 11.91/1.99  fof(f45,plain,(
% 11.91/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f33])).
% 11.91/1.99  
% 11.91/1.99  fof(f7,axiom,(
% 11.91/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f36,plain,(
% 11.91/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.91/1.99    inference(nnf_transformation,[],[f7])).
% 11.91/1.99  
% 11.91/1.99  fof(f37,plain,(
% 11.91/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.91/1.99    inference(flattening,[],[f36])).
% 11.91/1.99  
% 11.91/1.99  fof(f54,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.91/1.99    inference(cnf_transformation,[],[f37])).
% 11.91/1.99  
% 11.91/1.99  fof(f95,plain,(
% 11.91/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.91/1.99    inference(equality_resolution,[],[f54])).
% 11.91/1.99  
% 11.91/1.99  fof(f2,axiom,(
% 11.91/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f46,plain,(
% 11.91/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f2])).
% 11.91/1.99  
% 11.91/1.99  fof(f14,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f26,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f14])).
% 11.91/1.99  
% 11.91/1.99  fof(f27,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f26])).
% 11.91/1.99  
% 11.91/1.99  fof(f66,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f27])).
% 11.91/1.99  
% 11.91/1.99  fof(f16,conjecture,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f17,negated_conjecture,(
% 11.91/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 11.91/1.99    inference(negated_conjecture,[],[f16])).
% 11.91/1.99  
% 11.91/1.99  fof(f30,plain,(
% 11.91/1.99    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f17])).
% 11.91/1.99  
% 11.91/1.99  fof(f31,plain,(
% 11.91/1.99    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f30])).
% 11.91/1.99  
% 11.91/1.99  fof(f41,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK4) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK4,X0,k1_tarski(X1)) & v1_funct_1(sK4))) )),
% 11.91/1.99    introduced(choice_axiom,[])).
% 11.91/1.99  
% 11.91/1.99  fof(f40,plain,(
% 11.91/1.99    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(X3,sK1,k1_tarski(sK2)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3))),
% 11.91/1.99    introduced(choice_axiom,[])).
% 11.91/1.99  
% 11.91/1.99  fof(f42,plain,(
% 11.91/1.99    (k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3)),
% 11.91/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f41,f40])).
% 11.91/1.99  
% 11.91/1.99  fof(f75,plain,(
% 11.91/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f3,axiom,(
% 11.91/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f47,plain,(
% 11.91/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f3])).
% 11.91/1.99  
% 11.91/1.99  fof(f4,axiom,(
% 11.91/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f48,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f4])).
% 11.91/1.99  
% 11.91/1.99  fof(f5,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f49,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f5])).
% 11.91/1.99  
% 11.91/1.99  fof(f77,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.91/1.99    inference(definition_unfolding,[],[f48,f49])).
% 11.91/1.99  
% 11.91/1.99  fof(f78,plain,(
% 11.91/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.91/1.99    inference(definition_unfolding,[],[f47,f77])).
% 11.91/1.99  
% 11.91/1.99  fof(f90,plain,(
% 11.91/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 11.91/1.99    inference(definition_unfolding,[],[f75,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f73,plain,(
% 11.91/1.99    v1_funct_1(sK4)),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f74,plain,(
% 11.91/1.99    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f91,plain,(
% 11.91/1.99    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 11.91/1.99    inference(definition_unfolding,[],[f74,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f12,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f22,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f12])).
% 11.91/1.99  
% 11.91/1.99  fof(f23,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f22])).
% 11.91/1.99  
% 11.91/1.99  fof(f64,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f23])).
% 11.91/1.99  
% 11.91/1.99  fof(f88,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(definition_unfolding,[],[f64,f78,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f11,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f20,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f11])).
% 11.91/1.99  
% 11.91/1.99  fof(f21,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f20])).
% 11.91/1.99  
% 11.91/1.99  fof(f62,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f21])).
% 11.91/1.99  
% 11.91/1.99  fof(f52,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f37])).
% 11.91/1.99  
% 11.91/1.99  fof(f53,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.91/1.99    inference(cnf_transformation,[],[f37])).
% 11.91/1.99  
% 11.91/1.99  fof(f96,plain,(
% 11.91/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.91/1.99    inference(equality_resolution,[],[f53])).
% 11.91/1.99  
% 11.91/1.99  fof(f6,axiom,(
% 11.91/1.99    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f18,plain,(
% 11.91/1.99    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.91/1.99    inference(ennf_transformation,[],[f6])).
% 11.91/1.99  
% 11.91/1.99  fof(f34,plain,(
% 11.91/1.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)))),
% 11.91/1.99    introduced(choice_axiom,[])).
% 11.91/1.99  
% 11.91/1.99  fof(f35,plain,(
% 11.91/1.99    ! [X0,X1] : ((sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.91/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f34])).
% 11.91/1.99  
% 11.91/1.99  fof(f50,plain,(
% 11.91/1.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.91/1.99    inference(cnf_transformation,[],[f35])).
% 11.91/1.99  
% 11.91/1.99  fof(f80,plain,(
% 11.91/1.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 11.91/1.99    inference(definition_unfolding,[],[f50,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f72,plain,(
% 11.91/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f92,plain,(
% 11.91/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 11.91/1.99    inference(definition_unfolding,[],[f72,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f15,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f28,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f15])).
% 11.91/1.99  
% 11.91/1.99  fof(f29,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f28])).
% 11.91/1.99  
% 11.91/1.99  fof(f70,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f29])).
% 11.91/1.99  
% 11.91/1.99  fof(f71,plain,(
% 11.91/1.99    v1_funct_1(sK3)),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f76,plain,(
% 11.91/1.99    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)),
% 11.91/1.99    inference(cnf_transformation,[],[f42])).
% 11.91/1.99  
% 11.91/1.99  fof(f89,plain,(
% 11.91/1.99    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 11.91/1.99    inference(definition_unfolding,[],[f76,f78,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f69,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f29])).
% 11.91/1.99  
% 11.91/1.99  fof(f68,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f29])).
% 11.91/1.99  
% 11.91/1.99  fof(f10,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f38,plain,(
% 11.91/1.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.91/1.99    inference(nnf_transformation,[],[f10])).
% 11.91/1.99  
% 11.91/1.99  fof(f39,plain,(
% 11.91/1.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.91/1.99    inference(flattening,[],[f38])).
% 11.91/1.99  
% 11.91/1.99  fof(f61,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f39])).
% 11.91/1.99  
% 11.91/1.99  fof(f85,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.91/1.99    inference(definition_unfolding,[],[f61,f77])).
% 11.91/1.99  
% 11.91/1.99  fof(f13,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f24,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.91/1.99    inference(ennf_transformation,[],[f13])).
% 11.91/1.99  
% 11.91/1.99  fof(f25,plain,(
% 11.91/1.99    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.91/1.99    inference(flattening,[],[f24])).
% 11.91/1.99  
% 11.91/1.99  fof(f65,plain,(
% 11.91/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.91/1.99    inference(cnf_transformation,[],[f25])).
% 11.91/1.99  
% 11.91/1.99  fof(f43,plain,(
% 11.91/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.91/1.99    inference(cnf_transformation,[],[f33])).
% 11.91/1.99  
% 11.91/1.99  fof(f94,plain,(
% 11.91/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.91/1.99    inference(equality_resolution,[],[f43])).
% 11.91/1.99  
% 11.91/1.99  fof(f51,plain,(
% 11.91/1.99    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.91/1.99    inference(cnf_transformation,[],[f35])).
% 11.91/1.99  
% 11.91/1.99  fof(f79,plain,(
% 11.91/1.99    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 11.91/1.99    inference(definition_unfolding,[],[f51,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f9,axiom,(
% 11.91/1.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f58,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 11.91/1.99    inference(cnf_transformation,[],[f9])).
% 11.91/1.99  
% 11.91/1.99  fof(f83,plain,(
% 11.91/1.99    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 11.91/1.99    inference(definition_unfolding,[],[f58,f77,f77,f78])).
% 11.91/1.99  
% 11.91/1.99  fof(f8,axiom,(
% 11.91/1.99    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 11.91/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.91/1.99  
% 11.91/1.99  fof(f19,plain,(
% 11.91/1.99    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 11.91/1.99    inference(ennf_transformation,[],[f8])).
% 11.91/1.99  
% 11.91/1.99  fof(f56,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = X0) )),
% 11.91/1.99    inference(cnf_transformation,[],[f19])).
% 11.91/1.99  
% 11.91/1.99  fof(f81,plain,(
% 11.91/1.99    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0) )),
% 11.91/1.99    inference(definition_unfolding,[],[f56,f78])).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1088,plain,
% 11.91/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.91/1.99      theory(equality) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_0,plain,
% 11.91/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.91/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2302,plain,
% 11.91/1.99      ( ~ r1_tarski(X0,X1)
% 11.91/1.99      | ~ r1_tarski(X2,X0)
% 11.91/1.99      | ~ r1_tarski(X0,X2)
% 11.91/1.99      | r1_tarski(X2,X1) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_1088,c_0]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_6,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.91/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2304,plain,
% 11.91/1.99      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1)
% 11.91/1.99      | ~ r1_tarski(k1_xboole_0,X1) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_1088,c_6]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3,plain,
% 11.91/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.91/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2414,plain,
% 11.91/1.99      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1) ),
% 11.91/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_2304,c_3]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_9919,plain,
% 11.91/1.99      ( r1_tarski(X0,X1)
% 11.91/1.99      | ~ r1_tarski(X0,k2_zfmisc_1(X2,k1_xboole_0))
% 11.91/1.99      | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_2302,c_2414]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1087,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2759,plain,
% 11.91/1.99      ( X0 != k1_xboole_0 | k2_zfmisc_1(X1,k1_xboole_0) = X0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_1087,c_6]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1086,plain,( X0 = X0 ),theory(equality) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2761,plain,
% 11.91/1.99      ( X0 != X1 | X1 = X0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_1087,c_1086]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3257,plain,
% 11.91/1.99      ( X0 = k2_zfmisc_1(X1,k1_xboole_0) | X0 != k1_xboole_0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_2759,c_2761]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3512,plain,
% 11.91/1.99      ( r1_tarski(X0,X1)
% 11.91/1.99      | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1)
% 11.91/1.99      | X0 != k1_xboole_0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_3257,c_1088]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1097,plain,
% 11.91/1.99      ( X0 != X1
% 11.91/1.99      | X2 != X3
% 11.91/1.99      | X4 != X5
% 11.91/1.99      | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
% 11.91/1.99      theory(equality) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1090,plain,
% 11.91/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.91/1.99      theory(equality) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_6352,plain,
% 11.91/1.99      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 11.91/1.99      | r2_hidden(X4,k5_partfun1(X5,X6,X7))
% 11.91/1.99      | X5 != X1
% 11.91/1.99      | X4 != X0
% 11.91/1.99      | X6 != X2
% 11.91/1.99      | X7 != X3 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_1097,c_1090]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_21,plain,
% 11.91/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.91/1.99      | ~ r1_partfun1(X3,X0)
% 11.91/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 11.91/1.99      | ~ v1_funct_1(X3)
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k1_xboole_0 = X2 ),
% 11.91/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_26,negated_conjecture,
% 11.91/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 11.91/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7744,plain,
% 11.91/1.99      ( ~ v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 11.91/1.99      | ~ r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(sK4)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_21,c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_28,negated_conjecture,
% 11.91/1.99      ( v1_funct_1(sK4) ),
% 11.91/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_27,negated_conjecture,
% 11.91/1.99      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 11.91/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_525,plain,
% 11.91/1.99      ( ~ r1_partfun1(X0,X1)
% 11.91/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.91/1.99      | r2_hidden(X1,k5_partfun1(X2,X3,X0))
% 11.91/1.99      | ~ v1_funct_1(X1)
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) != X3
% 11.91/1.99      | sK1 != X2
% 11.91/1.99      | sK4 != X1
% 11.91/1.99      | k1_xboole_0 = X3 ),
% 11.91/1.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_526,plain,
% 11.91/1.99      ( ~ r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(sK4)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(unflattening,[status(thm)],[c_525]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_530,plain,
% 11.91/1.99      ( ~ v1_funct_1(X0)
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_526,c_28,c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_531,plain,
% 11.91/1.99      ( ~ r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_530]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1517,plain,
% 11.91/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_18,plain,
% 11.91/1.99      ( r1_partfun1(X0,X1)
% 11.91/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(X1) ),
% 11.91/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1524,plain,
% 11.91/1.99      ( r1_partfun1(X0,X1) = iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7114,plain,
% 11.91/1.99      ( r1_partfun1(X0,sK4) = iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1524]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7183,plain,
% 11.91/1.99      ( r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(sK4) ),
% 11.91/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_7114]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7853,plain,
% 11.91/1.99      ( ~ v1_funct_1(X0)
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_7744,c_28,c_26,c_526,c_7183]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7854,plain,
% 11.91/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_7853]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7879,plain,
% 11.91/1.99      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4))
% 11.91/1.99      | ~ v1_funct_1(sK4)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_7854,c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7884,plain,
% 11.91/1.99      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4))
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_7879,c_28]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_32699,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 11.91/1.99      | X2 != k2_enumset1(sK2,sK2,sK2,sK2)
% 11.91/1.99      | X1 != sK1
% 11.91/1.99      | X0 != sK4
% 11.91/1.99      | X3 != sK4
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_6352,c_7884]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_17,plain,
% 11.91/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | v1_partfun1(X0,X1)
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k1_xboole_0 = X2 ),
% 11.91/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5067,plain,
% 11.91/1.99      ( ~ v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 11.91/1.99      | v1_partfun1(sK4,sK1)
% 11.91/1.99      | ~ v1_funct_1(sK4)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_17,c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_552,plain,
% 11.91/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | v1_partfun1(X0,X1)
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) != X2
% 11.91/1.99      | sK1 != X1
% 11.91/1.99      | sK4 != X0
% 11.91/1.99      | k1_xboole_0 = X2 ),
% 11.91/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_553,plain,
% 11.91/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | v1_partfun1(sK4,sK1)
% 11.91/1.99      | ~ v1_funct_1(sK4)
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(unflattening,[status(thm)],[c_552]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_555,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_553,c_28,c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5094,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_5067,c_28,c_26,c_553]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5198,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_5094,c_2761]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5388,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1)
% 11.91/1.99      | X0 != k1_xboole_0
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = X0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_5198,c_1087]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5200,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1)
% 11.91/1.99      | X0 != k2_enumset1(sK2,sK2,sK2,sK2)
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_5094,c_1087]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_10617,plain,
% 11.91/1.99      ( v1_partfun1(sK4,sK1)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_5388,c_5200]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_8,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0
% 11.91/1.99      | k1_xboole_0 = X1 ),
% 11.91/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_69,plain,
% 11.91/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7,plain,
% 11.91/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.91/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_70,plain,
% 11.91/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3147,plain,
% 11.91/1.99      ( X0 != X1
% 11.91/1.99      | X0 = k2_enumset1(sK2,sK2,sK2,sK2)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) != X1 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1087]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3148,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
% 11.91/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_3147]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_13930,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_10617,c_69,c_70,c_3148]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5,plain,
% 11.91/1.99      ( r2_hidden(sK0(X0,X1),X0)
% 11.91/1.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1530,plain,
% 11.91/1.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 11.91/1.99      | k1_xboole_0 = X1
% 11.91/1.99      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_29,negated_conjecture,
% 11.91/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 11.91/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1514,plain,
% 11.91/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_22,plain,
% 11.91/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.91/1.99      | ~ v1_funct_1(X0) ),
% 11.91/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1520,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.91/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.91/1.99      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3417,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1514,c_1520]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_30,negated_conjecture,
% 11.91/1.99      ( v1_funct_1(sK3) ),
% 11.91/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_31,plain,
% 11.91/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3972,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_3417,c_31]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3973,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_3972]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3980,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1530,c_3973]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1521,plain,
% 11.91/1.99      ( k1_xboole_0 = X0
% 11.91/1.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 11.91/1.99      | r1_partfun1(X3,X1) != iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.91/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.91/1.99      | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top
% 11.91/1.99      | v1_funct_1(X3) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4437,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 11.91/1.99      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_3980,c_1521]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25,negated_conjecture,
% 11.91/1.99      ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1791,plain,
% 11.91/1.99      ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4))
% 11.91/1.99      | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1792,plain,
% 11.91/1.99      ( k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 11.91/1.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1895,plain,
% 11.91/1.99      ( ~ r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4))
% 11.91/1.99      | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4))
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1088]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1896,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0
% 11.91/1.99      | r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 11.91/1.99      | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1898,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k1_xboole_0
% 11.91/1.99      | r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 11.91/1.99      | r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1896]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2250,plain,
% 11.91/1.99      ( r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2253,plain,
% 11.91/1.99      ( r1_tarski(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_2250]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_23,plain,
% 11.91/1.99      ( v1_funct_2(X0,X1,X2)
% 11.91/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 11.91/1.99      | ~ v1_funct_1(X3) ),
% 11.91/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1519,plain,
% 11.91/1.99      ( v1_funct_2(X0,X1,X2) = iProver_top
% 11.91/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
% 11.91/1.99      | v1_funct_1(X3) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2659,plain,
% 11.91/1.99      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1514,c_1519]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2974,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2659,c_31]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2975,plain,
% 11.91/1.99      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_2974]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3464,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1530,c_2975]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24,plain,
% 11.91/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.91/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | v1_funct_1(X3) ),
% 11.91/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1518,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.91/1.99      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(X3) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2016,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) = iProver_top
% 11.91/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1514,c_1518]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2401,plain,
% 11.91/1.99      ( v1_funct_1(X0) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2016,c_31]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2402,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) = iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_2401]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3465,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1530,c_2402]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4434,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 11.91/1.99      | r1_partfun1(X0,sK4) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1521]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_33,plain,
% 11.91/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_34,plain,
% 11.91/1.99      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_35,plain,
% 11.91/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1865,plain,
% 11.91/1.99      ( r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 11.91/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(sK4) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2139,plain,
% 11.91/1.99      ( r1_partfun1(X0,sK4)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(sK4) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1865]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2140,plain,
% 11.91/1.99      ( r1_partfun1(X0,sK4) = iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_2139]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4991,plain,
% 11.91/1.99      ( v1_funct_1(X0) != iProver_top
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_4434,c_33,c_34,c_35,c_2140]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4992,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_4991]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5002,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 11.91/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1514,c_4992]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_13,plain,
% 11.91/1.99      ( ~ r2_hidden(X0,X1)
% 11.91/1.99      | ~ r2_hidden(X2,X1)
% 11.91/1.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 11.91/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4350,plain,
% 11.91/1.99      ( ~ r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | ~ r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_8884,plain,
% 11.91/1.99      ( ~ r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_4350]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_8885,plain,
% 11.91/1.99      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.91/1.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_8884]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_7117,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_3980,c_1524]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_10105,plain,
% 11.91/1.99      ( v1_funct_1(X1) != iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_7117,c_3465]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_10106,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_10105]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24189,plain,
% 11.91/1.99      ( v1_funct_1(X1) != iProver_top
% 11.91/1.99      | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_4437,c_31,c_25,c_1792,c_1898,c_2253,c_3464,c_3465,c_5002,
% 11.91/1.99                 c_8885,c_10106]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24190,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | r2_hidden(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X1)) = iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_24189]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3416,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1520]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3839,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_3416,c_33]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3840,plain,
% 11.91/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_3839]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24202,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_24190,c_3840]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_32,plain,
% 11.91/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24205,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 11.91/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_24190,c_3973]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25139,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_24202,c_31,c_25,c_1792,c_1898,c_2253,c_3980,c_5002,c_8885]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_19,plain,
% 11.91/1.99      ( ~ r1_partfun1(X0,X1)
% 11.91/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.91/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.91/1.99      | ~ v1_partfun1(X1,X2)
% 11.91/1.99      | ~ v1_partfun1(X0,X2)
% 11.91/1.99      | ~ v1_funct_1(X0)
% 11.91/1.99      | ~ v1_funct_1(X1)
% 11.91/1.99      | X1 = X0 ),
% 11.91/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1523,plain,
% 11.91/1.99      ( X0 = X1
% 11.91/1.99      | r1_partfun1(X1,X0) != iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.91/1.99      | v1_partfun1(X0,X2) != iProver_top
% 11.91/1.99      | v1_partfun1(X1,X2) != iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5616,plain,
% 11.91/1.99      ( sK4 = X0
% 11.91/1.99      | r1_partfun1(X0,sK4) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_partfun1(X0,sK1) != iProver_top
% 11.91/1.99      | v1_partfun1(sK4,sK1) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1523]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_6279,plain,
% 11.91/1.99      ( v1_funct_1(X0) != iProver_top
% 11.91/1.99      | v1_partfun1(sK4,sK1) != iProver_top
% 11.91/1.99      | v1_partfun1(X0,sK1) != iProver_top
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | sK4 = X0 ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_5616,c_33,c_35,c_2140]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_6280,plain,
% 11.91/1.99      ( sK4 = X0
% 11.91/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_partfun1(X0,sK1) != iProver_top
% 11.91/1.99      | v1_partfun1(sK4,sK1) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_6279]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25158,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 11.91/1.99      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 11.91/1.99      | v1_partfun1(sK4,sK1) != iProver_top
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_25139,c_6280]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_5199,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | v1_partfun1(sK4,sK1) = iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_5198]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2015,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) = iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1518]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2268,plain,
% 11.91/1.99      ( v1_funct_1(X0) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2015,c_33]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2269,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | v1_funct_1(X0) = iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_2268]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24204,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_24190,c_2269]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25033,plain,
% 11.91/1.99      ( v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_24204,c_33,c_35]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25034,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_25033]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2658,plain,
% 11.91/1.99      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_1517,c_1519]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2965,plain,
% 11.91/1.99      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 11.91/1.99      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2658,c_33]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2966,plain,
% 11.91/1.99      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 11.91/1.99      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_2965]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_24203,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 11.91/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 11.91/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_24190,c_2966]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25129,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_24203,c_31,c_25,c_1792,c_1898,c_2253,c_3464,c_5002,c_8885]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1525,plain,
% 11.91/1.99      ( k1_xboole_0 = X0
% 11.91/1.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 11.91/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.91/1.99      | v1_partfun1(X1,X2) = iProver_top
% 11.91/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.91/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_25153,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 11.91/1.99      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
% 11.91/1.99      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_25139,c_1525]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_26451,plain,
% 11.91/1.99      ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_25158,c_5199,c_25034,c_25129,c_25153]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_26452,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 11.91/1.99      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 11.91/1.99      inference(renaming,[status(thm)],[c_26451]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_26512,plain,
% 11.91/1.99      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
% 11.91/1.99      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_26452,c_25]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_28473,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 11.91/1.99      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) = sK4 ),
% 11.91/1.99      inference(equality_resolution,[status(thm)],[c_26512]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1940,plain,
% 11.91/1.99      ( ~ r1_tarski(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2389,plain,
% 11.91/1.99      ( ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1940]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f94]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2390,plain,
% 11.91/1.99      ( r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_1946,plain,
% 11.91/1.99      ( X0 != X1
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X1
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0 ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1087]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2458,plain,
% 11.91/1.99      ( X0 != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = X0
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2460,plain,
% 11.91/1.99      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 11.91/1.99      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 11.91/1.99      | k1_xboole_0 != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(instantiation,[status(thm)],[c_2458]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4,plain,
% 11.91/1.99      ( k2_enumset1(X0,X0,X0,X0) = X1 | sK0(X1,X0) != X0 | k1_xboole_0 = X1 ),
% 11.91/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_4836,plain,
% 11.91/1.99      ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) != sK4
% 11.91/1.99      | k1_xboole_0 = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_4,c_25]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_28742,plain,
% 11.91/1.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_28473,c_31,c_25,c_1792,c_1898,c_2253,c_2389,c_2390,c_2460,
% 11.91/1.99                 c_4836,c_5002,c_8885]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_32858,plain,
% 11.91/1.99      ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_32699,c_31,c_25,c_69,c_70,c_1792,c_1898,c_2253,c_2389,
% 11.91/1.99                 c_2390,c_2460,c_3148,c_4836,c_5002,c_8885,c_28473]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_32870,plain,
% 11.91/1.99      ( X0 != k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_32858,c_1087]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_11,plain,
% 11.91/1.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 11.91/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_9,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2701,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_11,c_9]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_3637,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3))) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_11,c_2701]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_9637,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k2_enumset1(X4,X4,X4,X4))) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_11,c_3637]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_29250,plain,
% 11.91/1.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X3,X3,X3,X3)),k1_xboole_0)) != k1_xboole_0
% 11.91/1.99      | k1_xboole_0 = X0 ),
% 11.91/1.99      inference(superposition,[status(thm)],[c_28742,c_9637]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_29354,plain,
% 11.91/1.99      ( k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 11.91/1.99      inference(demodulation,[status(thm)],[c_29250,c_6]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_29355,plain,
% 11.91/1.99      ( k1_xboole_0 = X0 ),
% 11.91/1.99      inference(equality_resolution_simp,[status(thm)],[c_29354]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_33306,plain,
% 11.91/1.99      ( k1_xboole_0 = X0 ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_32870,c_29355]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_33361,plain,
% 11.91/1.99      ( X0 = k1_xboole_0 ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_33306,c_2761]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_44200,plain,
% 11.91/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_zfmisc_1(X2,k1_xboole_0),X1) ),
% 11.91/1.99      inference(global_propositional_subsumption,
% 11.91/1.99                [status(thm)],
% 11.91/1.99                [c_9919,c_3512,c_33361]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_44206,plain,
% 11.91/1.99      ( r1_tarski(X0,X1) ),
% 11.91/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_44200,c_2414]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_2284,plain,
% 11.91/1.99      ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 11.91/1.99      | ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.91/1.99      inference(resolution,[status(thm)],[c_0,c_25]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_44267,plain,
% 11.91/1.99      ( ~ r1_tarski(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.91/1.99      inference(backward_subsumption_resolution,[status(thm)],[c_44206,c_2284]) ).
% 11.91/1.99  
% 11.91/1.99  cnf(c_46729,plain,
% 11.91/1.99      ( $false ),
% 11.91/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_44267,c_44206]) ).
% 11.91/1.99  
% 11.91/1.99  
% 11.91/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.91/1.99  
% 11.91/1.99  ------                               Statistics
% 11.91/1.99  
% 11.91/1.99  ------ Selected
% 11.91/1.99  
% 11.91/1.99  total_time:                             1.349
% 11.91/1.99  
%------------------------------------------------------------------------------
