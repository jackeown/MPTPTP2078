%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:52 EST 2020

% Result     : Theorem 15.86s
% Output     : CNFRefutation 15.86s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2964)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f34,f43,f42])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f65,f79,f79])).

fof(f75,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f15,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f77,f79,f79])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2435,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2422,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2425,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4161,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2425])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4478,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4161,c_32,c_34,c_2964])).

cnf(c_4479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4478])).

cnf(c_4486,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_4479])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2430,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6444,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_2430])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2424,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3382,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2424])).

cnf(c_3633,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3382,c_32])).

cnf(c_3634,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3633])).

cnf(c_4229,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_3634])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2423,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2869,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2423])).

cnf(c_3036,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2869,c_32])).

cnf(c_3037,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3036])).

cnf(c_4230,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_3037])).

cnf(c_13185,plain,
    ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6444,c_4229,c_4230])).

cnf(c_13186,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_13185])).

cnf(c_18,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2428,plain,
    ( X0 = X1
    | r1_partfun1(X1,X0) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6281,plain,
    ( sK4 = X0
    | r1_partfun1(X0,sK4) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2428])).

cnf(c_17,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2429,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6690,plain,
    ( r1_partfun1(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2429])).

cnf(c_7596,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6281,c_32,c_34,c_3245])).

cnf(c_7597,plain,
    ( sK4 = X0
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7596])).

cnf(c_7611,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_7597])).

cnf(c_10480,plain,
    ( v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7611,c_4230])).

cnf(c_10481,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10480])).

cnf(c_13196,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13186,c_10481])).

cnf(c_6442,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK4,sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2430])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_33,plain,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8367,plain,
    ( v1_partfun1(sK4,sK1) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6442,c_32,c_33])).

cnf(c_8368,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_partfun1(sK4,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_8367])).

cnf(c_13682,plain,
    ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13196,c_8368])).

cnf(c_13683,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4 ),
    inference(renaming,[status(thm)],[c_13682])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13692,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK4 != X0 ),
    inference(superposition,[status(thm)],[c_13683,c_5])).

cnf(c_15133,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_13692])).

cnf(c_15623,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15133,c_4479])).

cnf(c_16548,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK4 = X0
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15623,c_7597])).

cnf(c_15624,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15133,c_3634])).

cnf(c_15625,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15133,c_3037])).

cnf(c_16545,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(X0,sK1) = iProver_top
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15623,c_2430])).

cnf(c_18474,plain,
    ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | sK4 = X0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16548,c_7597,c_8368,c_15623,c_15624,c_15625,c_16545])).

cnf(c_18475,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18474])).

cnf(c_18484,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4 ),
    inference(superposition,[status(thm)],[c_2435,c_18475])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2426,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5155,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2426])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3244,plain,
    ( r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3245,plain,
    ( r1_partfun1(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3244])).

cnf(c_5649,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5155,c_32,c_33,c_34,c_3245])).

cnf(c_5650,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5649])).

cnf(c_5661,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_5650])).

cnf(c_5728,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5661,c_32])).

cnf(c_5729,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5728])).

cnf(c_19963,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18484,c_5729])).

cnf(c_12,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2434,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2432,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2432])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2436,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3920,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_2436])).

cnf(c_23717,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19963,c_3920])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_2425])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4651,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4162,c_30,c_31,c_2979])).

cnf(c_4652,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4651])).

cnf(c_4659,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_4652])).

cnf(c_6445,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4659,c_2430])).

cnf(c_3383,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_2424])).

cnf(c_3804,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_30])).

cnf(c_3805,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3804])).

cnf(c_4231,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_3805])).

cnf(c_2870,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_2423])).

cnf(c_3093,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2870,c_30])).

cnf(c_3094,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3093])).

cnf(c_4232,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_3094])).

cnf(c_33443,plain,
    ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6445,c_4231,c_4232])).

cnf(c_33444,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_33443])).

cnf(c_7612,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4659,c_7597])).

cnf(c_10810,plain,
    ( v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7612,c_4232])).

cnf(c_10811,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10810])).

cnf(c_33459,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_33444,c_10811])).

cnf(c_62354,plain,
    ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33459,c_8368])).

cnf(c_62355,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(renaming,[status(thm)],[c_62354])).

cnf(c_24,negated_conjecture,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_62457,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(superposition,[status(thm)],[c_62355,c_24])).

cnf(c_64914,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(superposition,[status(thm)],[c_23717,c_62457])).

cnf(c_1820,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2688,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_2843,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_1819,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2844,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_64919,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_62457])).

cnf(c_65242,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_64919,c_5])).

cnf(c_65565,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64914,c_24,c_2843,c_2844,c_65242])).

cnf(c_65622,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_65565,c_3094])).

cnf(c_65623,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_65565,c_24])).

cnf(c_5662,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_5650])).

cnf(c_5792,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5662,c_30])).

cnf(c_5793,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5792])).

cnf(c_65616,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_65565,c_5793])).

cnf(c_67634,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_65616,c_3920])).

cnf(c_67640,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_65622,c_65623,c_67634])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_68609,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_67640,c_11])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_68733,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_68609,c_8])).

cnf(c_68734,plain,
    ( k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_68733])).

cnf(c_3257,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2432])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2439,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3546,plain,
    ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
    | r1_tarski(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_2439])).

cnf(c_67734,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) = sK4
    | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67640,c_3546])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_67779,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67734,c_7])).

cnf(c_3144,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3145,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3144])).

cnf(c_3147,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3145])).

cnf(c_3570,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3571,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3570])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3620,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3623,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3620])).

cnf(c_67741,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67640,c_2422])).

cnf(c_67753,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67741,c_7])).

cnf(c_70655,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_67779,c_3147,c_3571,c_3623,c_67753])).

cnf(c_2420,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_70672,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_70655,c_2420])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2438,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2425])).

cnf(c_4178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4163,c_7])).

cnf(c_5579,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
    | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(sK0(k5_partfun1(X1,k1_xboole_0,X2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_4178])).

cnf(c_22972,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
    | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK0(k5_partfun1(X1,k1_xboole_0,X2),X0),k1_xboole_0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5579,c_2432])).

cnf(c_23069,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
    | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
    | sK0(k5_partfun1(X1,k1_xboole_0,X2),X0) = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22972,c_2436])).

cnf(c_27740,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
    | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
    | sK0(k5_partfun1(X1,k1_xboole_0,X2),X0) = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_23069])).

cnf(c_27805,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
    | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_27740])).

cnf(c_70987,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
    | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_70672,c_27805])).

cnf(c_71481,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
    | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_70987,c_5])).

cnf(c_74178,plain,
    ( k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_71481,c_68734])).

cnf(c_74179,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
    | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_74178])).

cnf(c_74224,plain,
    ( k5_partfun1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_74179,c_67640])).

cnf(c_67744,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
    inference(demodulation,[status(thm)],[c_67640,c_24])).

cnf(c_70663,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
    inference(demodulation,[status(thm)],[c_70655,c_67744])).

cnf(c_3258,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_2432])).

cnf(c_3630,plain,
    ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_2439])).

cnf(c_67733,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67640,c_3630])).

cnf(c_67784,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67733,c_7])).

cnf(c_3600,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3601,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3600])).

cnf(c_3603,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_7123,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7126,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7123])).

cnf(c_9241,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_9242,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9241])).

cnf(c_9244,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9242])).

cnf(c_67742,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67640,c_2419])).

cnf(c_67750,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67742,c_7])).

cnf(c_70719,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_67784,c_3603,c_7126,c_9244,c_67750])).

cnf(c_71191,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_70663,c_70719])).

cnf(c_75560,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_74224,c_71191])).

cnf(c_77408,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_68734,c_75560])).

cnf(c_77544,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_77408])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 15.86/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.86/2.49  
% 15.86/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.86/2.49  
% 15.86/2.49  ------  iProver source info
% 15.86/2.49  
% 15.86/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.86/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.86/2.49  git: non_committed_changes: false
% 15.86/2.49  git: last_make_outside_of_git: false
% 15.86/2.49  
% 15.86/2.49  ------ 
% 15.86/2.49  
% 15.86/2.49  ------ Input Options
% 15.86/2.49  
% 15.86/2.49  --out_options                           all
% 15.86/2.49  --tptp_safe_out                         true
% 15.86/2.49  --problem_path                          ""
% 15.86/2.49  --include_path                          ""
% 15.86/2.49  --clausifier                            res/vclausify_rel
% 15.86/2.49  --clausifier_options                    --mode clausify
% 15.86/2.49  --stdin                                 false
% 15.86/2.49  --stats_out                             all
% 15.86/2.49  
% 15.86/2.49  ------ General Options
% 15.86/2.49  
% 15.86/2.49  --fof                                   false
% 15.86/2.49  --time_out_real                         305.
% 15.86/2.49  --time_out_virtual                      -1.
% 15.86/2.49  --symbol_type_check                     false
% 15.86/2.49  --clausify_out                          false
% 15.86/2.49  --sig_cnt_out                           false
% 15.86/2.49  --trig_cnt_out                          false
% 15.86/2.49  --trig_cnt_out_tolerance                1.
% 15.86/2.49  --trig_cnt_out_sk_spl                   false
% 15.86/2.49  --abstr_cl_out                          false
% 15.86/2.49  
% 15.86/2.49  ------ Global Options
% 15.86/2.49  
% 15.86/2.49  --schedule                              default
% 15.86/2.49  --add_important_lit                     false
% 15.86/2.49  --prop_solver_per_cl                    1000
% 15.86/2.49  --min_unsat_core                        false
% 15.86/2.49  --soft_assumptions                      false
% 15.86/2.49  --soft_lemma_size                       3
% 15.86/2.49  --prop_impl_unit_size                   0
% 15.86/2.49  --prop_impl_unit                        []
% 15.86/2.49  --share_sel_clauses                     true
% 15.86/2.49  --reset_solvers                         false
% 15.86/2.49  --bc_imp_inh                            [conj_cone]
% 15.86/2.49  --conj_cone_tolerance                   3.
% 15.86/2.49  --extra_neg_conj                        none
% 15.86/2.49  --large_theory_mode                     true
% 15.86/2.49  --prolific_symb_bound                   200
% 15.86/2.49  --lt_threshold                          2000
% 15.86/2.49  --clause_weak_htbl                      true
% 15.86/2.49  --gc_record_bc_elim                     false
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing Options
% 15.86/2.49  
% 15.86/2.49  --preprocessing_flag                    true
% 15.86/2.49  --time_out_prep_mult                    0.1
% 15.86/2.49  --splitting_mode                        input
% 15.86/2.49  --splitting_grd                         true
% 15.86/2.49  --splitting_cvd                         false
% 15.86/2.49  --splitting_cvd_svl                     false
% 15.86/2.49  --splitting_nvd                         32
% 15.86/2.49  --sub_typing                            true
% 15.86/2.49  --prep_gs_sim                           true
% 15.86/2.49  --prep_unflatten                        true
% 15.86/2.49  --prep_res_sim                          true
% 15.86/2.49  --prep_upred                            true
% 15.86/2.49  --prep_sem_filter                       exhaustive
% 15.86/2.49  --prep_sem_filter_out                   false
% 15.86/2.49  --pred_elim                             true
% 15.86/2.49  --res_sim_input                         true
% 15.86/2.49  --eq_ax_congr_red                       true
% 15.86/2.49  --pure_diseq_elim                       true
% 15.86/2.49  --brand_transform                       false
% 15.86/2.49  --non_eq_to_eq                          false
% 15.86/2.49  --prep_def_merge                        true
% 15.86/2.49  --prep_def_merge_prop_impl              false
% 15.86/2.49  --prep_def_merge_mbd                    true
% 15.86/2.49  --prep_def_merge_tr_red                 false
% 15.86/2.49  --prep_def_merge_tr_cl                  false
% 15.86/2.49  --smt_preprocessing                     true
% 15.86/2.49  --smt_ac_axioms                         fast
% 15.86/2.49  --preprocessed_out                      false
% 15.86/2.49  --preprocessed_stats                    false
% 15.86/2.49  
% 15.86/2.49  ------ Abstraction refinement Options
% 15.86/2.49  
% 15.86/2.49  --abstr_ref                             []
% 15.86/2.49  --abstr_ref_prep                        false
% 15.86/2.49  --abstr_ref_until_sat                   false
% 15.86/2.49  --abstr_ref_sig_restrict                funpre
% 15.86/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.86/2.49  --abstr_ref_under                       []
% 15.86/2.49  
% 15.86/2.49  ------ SAT Options
% 15.86/2.49  
% 15.86/2.49  --sat_mode                              false
% 15.86/2.49  --sat_fm_restart_options                ""
% 15.86/2.49  --sat_gr_def                            false
% 15.86/2.49  --sat_epr_types                         true
% 15.86/2.49  --sat_non_cyclic_types                  false
% 15.86/2.49  --sat_finite_models                     false
% 15.86/2.49  --sat_fm_lemmas                         false
% 15.86/2.49  --sat_fm_prep                           false
% 15.86/2.49  --sat_fm_uc_incr                        true
% 15.86/2.49  --sat_out_model                         small
% 15.86/2.49  --sat_out_clauses                       false
% 15.86/2.49  
% 15.86/2.49  ------ QBF Options
% 15.86/2.49  
% 15.86/2.49  --qbf_mode                              false
% 15.86/2.49  --qbf_elim_univ                         false
% 15.86/2.49  --qbf_dom_inst                          none
% 15.86/2.49  --qbf_dom_pre_inst                      false
% 15.86/2.49  --qbf_sk_in                             false
% 15.86/2.49  --qbf_pred_elim                         true
% 15.86/2.49  --qbf_split                             512
% 15.86/2.49  
% 15.86/2.49  ------ BMC1 Options
% 15.86/2.49  
% 15.86/2.49  --bmc1_incremental                      false
% 15.86/2.49  --bmc1_axioms                           reachable_all
% 15.86/2.49  --bmc1_min_bound                        0
% 15.86/2.49  --bmc1_max_bound                        -1
% 15.86/2.49  --bmc1_max_bound_default                -1
% 15.86/2.49  --bmc1_symbol_reachability              true
% 15.86/2.49  --bmc1_property_lemmas                  false
% 15.86/2.49  --bmc1_k_induction                      false
% 15.86/2.49  --bmc1_non_equiv_states                 false
% 15.86/2.49  --bmc1_deadlock                         false
% 15.86/2.49  --bmc1_ucm                              false
% 15.86/2.49  --bmc1_add_unsat_core                   none
% 15.86/2.49  --bmc1_unsat_core_children              false
% 15.86/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.86/2.49  --bmc1_out_stat                         full
% 15.86/2.49  --bmc1_ground_init                      false
% 15.86/2.49  --bmc1_pre_inst_next_state              false
% 15.86/2.49  --bmc1_pre_inst_state                   false
% 15.86/2.49  --bmc1_pre_inst_reach_state             false
% 15.86/2.49  --bmc1_out_unsat_core                   false
% 15.86/2.49  --bmc1_aig_witness_out                  false
% 15.86/2.49  --bmc1_verbose                          false
% 15.86/2.49  --bmc1_dump_clauses_tptp                false
% 15.86/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.86/2.49  --bmc1_dump_file                        -
% 15.86/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.86/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.86/2.49  --bmc1_ucm_extend_mode                  1
% 15.86/2.49  --bmc1_ucm_init_mode                    2
% 15.86/2.49  --bmc1_ucm_cone_mode                    none
% 15.86/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.86/2.49  --bmc1_ucm_relax_model                  4
% 15.86/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.86/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.86/2.49  --bmc1_ucm_layered_model                none
% 15.86/2.49  --bmc1_ucm_max_lemma_size               10
% 15.86/2.49  
% 15.86/2.49  ------ AIG Options
% 15.86/2.49  
% 15.86/2.49  --aig_mode                              false
% 15.86/2.49  
% 15.86/2.49  ------ Instantiation Options
% 15.86/2.49  
% 15.86/2.49  --instantiation_flag                    true
% 15.86/2.49  --inst_sos_flag                         false
% 15.86/2.49  --inst_sos_phase                        true
% 15.86/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.86/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.86/2.49  --inst_lit_sel_side                     num_symb
% 15.86/2.49  --inst_solver_per_active                1400
% 15.86/2.49  --inst_solver_calls_frac                1.
% 15.86/2.49  --inst_passive_queue_type               priority_queues
% 15.86/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.86/2.49  --inst_passive_queues_freq              [25;2]
% 15.86/2.49  --inst_dismatching                      true
% 15.86/2.49  --inst_eager_unprocessed_to_passive     true
% 15.86/2.49  --inst_prop_sim_given                   true
% 15.86/2.49  --inst_prop_sim_new                     false
% 15.86/2.49  --inst_subs_new                         false
% 15.86/2.49  --inst_eq_res_simp                      false
% 15.86/2.49  --inst_subs_given                       false
% 15.86/2.49  --inst_orphan_elimination               true
% 15.86/2.49  --inst_learning_loop_flag               true
% 15.86/2.49  --inst_learning_start                   3000
% 15.86/2.49  --inst_learning_factor                  2
% 15.86/2.49  --inst_start_prop_sim_after_learn       3
% 15.86/2.49  --inst_sel_renew                        solver
% 15.86/2.49  --inst_lit_activity_flag                true
% 15.86/2.49  --inst_restr_to_given                   false
% 15.86/2.49  --inst_activity_threshold               500
% 15.86/2.49  --inst_out_proof                        true
% 15.86/2.49  
% 15.86/2.49  ------ Resolution Options
% 15.86/2.49  
% 15.86/2.49  --resolution_flag                       true
% 15.86/2.49  --res_lit_sel                           adaptive
% 15.86/2.49  --res_lit_sel_side                      none
% 15.86/2.49  --res_ordering                          kbo
% 15.86/2.49  --res_to_prop_solver                    active
% 15.86/2.49  --res_prop_simpl_new                    false
% 15.86/2.49  --res_prop_simpl_given                  true
% 15.86/2.49  --res_passive_queue_type                priority_queues
% 15.86/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.86/2.49  --res_passive_queues_freq               [15;5]
% 15.86/2.49  --res_forward_subs                      full
% 15.86/2.49  --res_backward_subs                     full
% 15.86/2.49  --res_forward_subs_resolution           true
% 15.86/2.49  --res_backward_subs_resolution          true
% 15.86/2.49  --res_orphan_elimination                true
% 15.86/2.49  --res_time_limit                        2.
% 15.86/2.49  --res_out_proof                         true
% 15.86/2.49  
% 15.86/2.49  ------ Superposition Options
% 15.86/2.49  
% 15.86/2.49  --superposition_flag                    true
% 15.86/2.49  --sup_passive_queue_type                priority_queues
% 15.86/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.86/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.86/2.49  --demod_completeness_check              fast
% 15.86/2.49  --demod_use_ground                      true
% 15.86/2.49  --sup_to_prop_solver                    passive
% 15.86/2.49  --sup_prop_simpl_new                    true
% 15.86/2.49  --sup_prop_simpl_given                  true
% 15.86/2.49  --sup_fun_splitting                     false
% 15.86/2.49  --sup_smt_interval                      50000
% 15.86/2.49  
% 15.86/2.49  ------ Superposition Simplification Setup
% 15.86/2.49  
% 15.86/2.49  --sup_indices_passive                   []
% 15.86/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.86/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_full_bw                           [BwDemod]
% 15.86/2.49  --sup_immed_triv                        [TrivRules]
% 15.86/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_immed_bw_main                     []
% 15.86/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.86/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.86/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.86/2.49  
% 15.86/2.49  ------ Combination Options
% 15.86/2.49  
% 15.86/2.49  --comb_res_mult                         3
% 15.86/2.49  --comb_sup_mult                         2
% 15.86/2.49  --comb_inst_mult                        10
% 15.86/2.49  
% 15.86/2.49  ------ Debug Options
% 15.86/2.49  
% 15.86/2.49  --dbg_backtrace                         false
% 15.86/2.49  --dbg_dump_prop_clauses                 false
% 15.86/2.49  --dbg_dump_prop_clauses_file            -
% 15.86/2.49  --dbg_out_stat                          false
% 15.86/2.49  ------ Parsing...
% 15.86/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.86/2.49  ------ Proving...
% 15.86/2.49  ------ Problem Properties 
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  clauses                                 29
% 15.86/2.49  conjectures                             6
% 15.86/2.49  EPR                                     6
% 15.86/2.49  Horn                                    24
% 15.86/2.49  unary                                   10
% 15.86/2.49  binary                                  6
% 15.86/2.49  lits                                    83
% 15.86/2.49  lits eq                                 20
% 15.86/2.49  fd_pure                                 0
% 15.86/2.49  fd_pseudo                               0
% 15.86/2.49  fd_cond                                 6
% 15.86/2.49  fd_pseudo_cond                          4
% 15.86/2.49  AC symbols                              0
% 15.86/2.49  
% 15.86/2.49  ------ Schedule dynamic 5 is on 
% 15.86/2.49  
% 15.86/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  ------ 
% 15.86/2.49  Current options:
% 15.86/2.49  ------ 
% 15.86/2.49  
% 15.86/2.49  ------ Input Options
% 15.86/2.49  
% 15.86/2.49  --out_options                           all
% 15.86/2.49  --tptp_safe_out                         true
% 15.86/2.49  --problem_path                          ""
% 15.86/2.49  --include_path                          ""
% 15.86/2.49  --clausifier                            res/vclausify_rel
% 15.86/2.49  --clausifier_options                    --mode clausify
% 15.86/2.49  --stdin                                 false
% 15.86/2.49  --stats_out                             all
% 15.86/2.49  
% 15.86/2.49  ------ General Options
% 15.86/2.49  
% 15.86/2.49  --fof                                   false
% 15.86/2.49  --time_out_real                         305.
% 15.86/2.49  --time_out_virtual                      -1.
% 15.86/2.49  --symbol_type_check                     false
% 15.86/2.49  --clausify_out                          false
% 15.86/2.49  --sig_cnt_out                           false
% 15.86/2.49  --trig_cnt_out                          false
% 15.86/2.49  --trig_cnt_out_tolerance                1.
% 15.86/2.49  --trig_cnt_out_sk_spl                   false
% 15.86/2.49  --abstr_cl_out                          false
% 15.86/2.49  
% 15.86/2.49  ------ Global Options
% 15.86/2.49  
% 15.86/2.49  --schedule                              default
% 15.86/2.49  --add_important_lit                     false
% 15.86/2.49  --prop_solver_per_cl                    1000
% 15.86/2.49  --min_unsat_core                        false
% 15.86/2.49  --soft_assumptions                      false
% 15.86/2.49  --soft_lemma_size                       3
% 15.86/2.49  --prop_impl_unit_size                   0
% 15.86/2.49  --prop_impl_unit                        []
% 15.86/2.49  --share_sel_clauses                     true
% 15.86/2.49  --reset_solvers                         false
% 15.86/2.49  --bc_imp_inh                            [conj_cone]
% 15.86/2.49  --conj_cone_tolerance                   3.
% 15.86/2.49  --extra_neg_conj                        none
% 15.86/2.49  --large_theory_mode                     true
% 15.86/2.49  --prolific_symb_bound                   200
% 15.86/2.49  --lt_threshold                          2000
% 15.86/2.49  --clause_weak_htbl                      true
% 15.86/2.49  --gc_record_bc_elim                     false
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing Options
% 15.86/2.49  
% 15.86/2.49  --preprocessing_flag                    true
% 15.86/2.49  --time_out_prep_mult                    0.1
% 15.86/2.49  --splitting_mode                        input
% 15.86/2.49  --splitting_grd                         true
% 15.86/2.49  --splitting_cvd                         false
% 15.86/2.49  --splitting_cvd_svl                     false
% 15.86/2.49  --splitting_nvd                         32
% 15.86/2.49  --sub_typing                            true
% 15.86/2.49  --prep_gs_sim                           true
% 15.86/2.49  --prep_unflatten                        true
% 15.86/2.49  --prep_res_sim                          true
% 15.86/2.49  --prep_upred                            true
% 15.86/2.49  --prep_sem_filter                       exhaustive
% 15.86/2.49  --prep_sem_filter_out                   false
% 15.86/2.49  --pred_elim                             true
% 15.86/2.49  --res_sim_input                         true
% 15.86/2.49  --eq_ax_congr_red                       true
% 15.86/2.49  --pure_diseq_elim                       true
% 15.86/2.49  --brand_transform                       false
% 15.86/2.49  --non_eq_to_eq                          false
% 15.86/2.49  --prep_def_merge                        true
% 15.86/2.49  --prep_def_merge_prop_impl              false
% 15.86/2.49  --prep_def_merge_mbd                    true
% 15.86/2.49  --prep_def_merge_tr_red                 false
% 15.86/2.49  --prep_def_merge_tr_cl                  false
% 15.86/2.49  --smt_preprocessing                     true
% 15.86/2.49  --smt_ac_axioms                         fast
% 15.86/2.49  --preprocessed_out                      false
% 15.86/2.49  --preprocessed_stats                    false
% 15.86/2.49  
% 15.86/2.49  ------ Abstraction refinement Options
% 15.86/2.49  
% 15.86/2.49  --abstr_ref                             []
% 15.86/2.49  --abstr_ref_prep                        false
% 15.86/2.49  --abstr_ref_until_sat                   false
% 15.86/2.49  --abstr_ref_sig_restrict                funpre
% 15.86/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.86/2.49  --abstr_ref_under                       []
% 15.86/2.49  
% 15.86/2.49  ------ SAT Options
% 15.86/2.49  
% 15.86/2.49  --sat_mode                              false
% 15.86/2.49  --sat_fm_restart_options                ""
% 15.86/2.49  --sat_gr_def                            false
% 15.86/2.49  --sat_epr_types                         true
% 15.86/2.49  --sat_non_cyclic_types                  false
% 15.86/2.49  --sat_finite_models                     false
% 15.86/2.49  --sat_fm_lemmas                         false
% 15.86/2.49  --sat_fm_prep                           false
% 15.86/2.49  --sat_fm_uc_incr                        true
% 15.86/2.49  --sat_out_model                         small
% 15.86/2.49  --sat_out_clauses                       false
% 15.86/2.49  
% 15.86/2.49  ------ QBF Options
% 15.86/2.49  
% 15.86/2.49  --qbf_mode                              false
% 15.86/2.49  --qbf_elim_univ                         false
% 15.86/2.49  --qbf_dom_inst                          none
% 15.86/2.49  --qbf_dom_pre_inst                      false
% 15.86/2.49  --qbf_sk_in                             false
% 15.86/2.49  --qbf_pred_elim                         true
% 15.86/2.49  --qbf_split                             512
% 15.86/2.49  
% 15.86/2.49  ------ BMC1 Options
% 15.86/2.49  
% 15.86/2.49  --bmc1_incremental                      false
% 15.86/2.49  --bmc1_axioms                           reachable_all
% 15.86/2.49  --bmc1_min_bound                        0
% 15.86/2.49  --bmc1_max_bound                        -1
% 15.86/2.49  --bmc1_max_bound_default                -1
% 15.86/2.49  --bmc1_symbol_reachability              true
% 15.86/2.49  --bmc1_property_lemmas                  false
% 15.86/2.49  --bmc1_k_induction                      false
% 15.86/2.49  --bmc1_non_equiv_states                 false
% 15.86/2.49  --bmc1_deadlock                         false
% 15.86/2.49  --bmc1_ucm                              false
% 15.86/2.49  --bmc1_add_unsat_core                   none
% 15.86/2.49  --bmc1_unsat_core_children              false
% 15.86/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.86/2.49  --bmc1_out_stat                         full
% 15.86/2.49  --bmc1_ground_init                      false
% 15.86/2.49  --bmc1_pre_inst_next_state              false
% 15.86/2.49  --bmc1_pre_inst_state                   false
% 15.86/2.49  --bmc1_pre_inst_reach_state             false
% 15.86/2.49  --bmc1_out_unsat_core                   false
% 15.86/2.49  --bmc1_aig_witness_out                  false
% 15.86/2.49  --bmc1_verbose                          false
% 15.86/2.49  --bmc1_dump_clauses_tptp                false
% 15.86/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.86/2.49  --bmc1_dump_file                        -
% 15.86/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.86/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.86/2.49  --bmc1_ucm_extend_mode                  1
% 15.86/2.49  --bmc1_ucm_init_mode                    2
% 15.86/2.49  --bmc1_ucm_cone_mode                    none
% 15.86/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.86/2.49  --bmc1_ucm_relax_model                  4
% 15.86/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.86/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.86/2.49  --bmc1_ucm_layered_model                none
% 15.86/2.49  --bmc1_ucm_max_lemma_size               10
% 15.86/2.49  
% 15.86/2.49  ------ AIG Options
% 15.86/2.49  
% 15.86/2.49  --aig_mode                              false
% 15.86/2.49  
% 15.86/2.49  ------ Instantiation Options
% 15.86/2.49  
% 15.86/2.49  --instantiation_flag                    true
% 15.86/2.49  --inst_sos_flag                         false
% 15.86/2.49  --inst_sos_phase                        true
% 15.86/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.86/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.86/2.49  --inst_lit_sel_side                     none
% 15.86/2.49  --inst_solver_per_active                1400
% 15.86/2.49  --inst_solver_calls_frac                1.
% 15.86/2.49  --inst_passive_queue_type               priority_queues
% 15.86/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.86/2.49  --inst_passive_queues_freq              [25;2]
% 15.86/2.49  --inst_dismatching                      true
% 15.86/2.49  --inst_eager_unprocessed_to_passive     true
% 15.86/2.49  --inst_prop_sim_given                   true
% 15.86/2.49  --inst_prop_sim_new                     false
% 15.86/2.49  --inst_subs_new                         false
% 15.86/2.49  --inst_eq_res_simp                      false
% 15.86/2.49  --inst_subs_given                       false
% 15.86/2.49  --inst_orphan_elimination               true
% 15.86/2.49  --inst_learning_loop_flag               true
% 15.86/2.49  --inst_learning_start                   3000
% 15.86/2.49  --inst_learning_factor                  2
% 15.86/2.49  --inst_start_prop_sim_after_learn       3
% 15.86/2.49  --inst_sel_renew                        solver
% 15.86/2.49  --inst_lit_activity_flag                true
% 15.86/2.49  --inst_restr_to_given                   false
% 15.86/2.49  --inst_activity_threshold               500
% 15.86/2.49  --inst_out_proof                        true
% 15.86/2.49  
% 15.86/2.49  ------ Resolution Options
% 15.86/2.49  
% 15.86/2.49  --resolution_flag                       false
% 15.86/2.49  --res_lit_sel                           adaptive
% 15.86/2.49  --res_lit_sel_side                      none
% 15.86/2.49  --res_ordering                          kbo
% 15.86/2.49  --res_to_prop_solver                    active
% 15.86/2.49  --res_prop_simpl_new                    false
% 15.86/2.49  --res_prop_simpl_given                  true
% 15.86/2.49  --res_passive_queue_type                priority_queues
% 15.86/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.86/2.49  --res_passive_queues_freq               [15;5]
% 15.86/2.49  --res_forward_subs                      full
% 15.86/2.49  --res_backward_subs                     full
% 15.86/2.49  --res_forward_subs_resolution           true
% 15.86/2.49  --res_backward_subs_resolution          true
% 15.86/2.49  --res_orphan_elimination                true
% 15.86/2.49  --res_time_limit                        2.
% 15.86/2.49  --res_out_proof                         true
% 15.86/2.49  
% 15.86/2.49  ------ Superposition Options
% 15.86/2.49  
% 15.86/2.49  --superposition_flag                    true
% 15.86/2.49  --sup_passive_queue_type                priority_queues
% 15.86/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.86/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.86/2.49  --demod_completeness_check              fast
% 15.86/2.49  --demod_use_ground                      true
% 15.86/2.49  --sup_to_prop_solver                    passive
% 15.86/2.49  --sup_prop_simpl_new                    true
% 15.86/2.49  --sup_prop_simpl_given                  true
% 15.86/2.49  --sup_fun_splitting                     false
% 15.86/2.49  --sup_smt_interval                      50000
% 15.86/2.49  
% 15.86/2.49  ------ Superposition Simplification Setup
% 15.86/2.49  
% 15.86/2.49  --sup_indices_passive                   []
% 15.86/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.86/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_full_bw                           [BwDemod]
% 15.86/2.49  --sup_immed_triv                        [TrivRules]
% 15.86/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_immed_bw_main                     []
% 15.86/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.86/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.86/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.86/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.86/2.49  
% 15.86/2.49  ------ Combination Options
% 15.86/2.49  
% 15.86/2.49  --comb_res_mult                         3
% 15.86/2.49  --comb_sup_mult                         2
% 15.86/2.49  --comb_inst_mult                        10
% 15.86/2.49  
% 15.86/2.49  ------ Debug Options
% 15.86/2.49  
% 15.86/2.49  --dbg_backtrace                         false
% 15.86/2.49  --dbg_dump_prop_clauses                 false
% 15.86/2.49  --dbg_dump_prop_clauses_file            -
% 15.86/2.49  --dbg_out_stat                          false
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  ------ Proving...
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  % SZS status Theorem for theBenchmark.p
% 15.86/2.49  
% 15.86/2.49   Resolution empty clause
% 15.86/2.49  
% 15.86/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.86/2.49  
% 15.86/2.49  fof(f7,axiom,(
% 15.86/2.49    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f20,plain,(
% 15.86/2.49    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.86/2.49    inference(ennf_transformation,[],[f7])).
% 15.86/2.49  
% 15.86/2.49  fof(f37,plain,(
% 15.86/2.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)))),
% 15.86/2.49    introduced(choice_axiom,[])).
% 15.86/2.49  
% 15.86/2.49  fof(f38,plain,(
% 15.86/2.49    ! [X0,X1] : ((sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.86/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f37])).
% 15.86/2.49  
% 15.86/2.49  fof(f53,plain,(
% 15.86/2.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.86/2.49    inference(cnf_transformation,[],[f38])).
% 15.86/2.49  
% 15.86/2.49  fof(f4,axiom,(
% 15.86/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f50,plain,(
% 15.86/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f4])).
% 15.86/2.49  
% 15.86/2.49  fof(f5,axiom,(
% 15.86/2.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f51,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f5])).
% 15.86/2.49  
% 15.86/2.49  fof(f6,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f52,plain,(
% 15.86/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f6])).
% 15.86/2.49  
% 15.86/2.49  fof(f78,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.86/2.49    inference(definition_unfolding,[],[f51,f52])).
% 15.86/2.49  
% 15.86/2.49  fof(f79,plain,(
% 15.86/2.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.86/2.49    inference(definition_unfolding,[],[f50,f78])).
% 15.86/2.49  
% 15.86/2.49  fof(f81,plain,(
% 15.86/2.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 15.86/2.49    inference(definition_unfolding,[],[f53,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f17,conjecture,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f18,negated_conjecture,(
% 15.86/2.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 15.86/2.49    inference(negated_conjecture,[],[f17])).
% 15.86/2.49  
% 15.86/2.49  fof(f33,plain,(
% 15.86/2.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f18])).
% 15.86/2.49  
% 15.86/2.49  fof(f34,plain,(
% 15.86/2.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f33])).
% 15.86/2.49  
% 15.86/2.49  fof(f43,plain,(
% 15.86/2.49    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK4) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK4,X0,k1_tarski(X1)) & v1_funct_1(sK4))) )),
% 15.86/2.49    introduced(choice_axiom,[])).
% 15.86/2.49  
% 15.86/2.49  fof(f42,plain,(
% 15.86/2.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(X3,sK1,k1_tarski(sK2)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3))),
% 15.86/2.49    introduced(choice_axiom,[])).
% 15.86/2.49  
% 15.86/2.49  fof(f44,plain,(
% 15.86/2.49    (k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3)),
% 15.86/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f34,f43,f42])).
% 15.86/2.49  
% 15.86/2.49  fof(f76,plain,(
% 15.86/2.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f87,plain,(
% 15.86/2.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 15.86/2.49    inference(definition_unfolding,[],[f76,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f16,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f31,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f16])).
% 15.86/2.49  
% 15.86/2.49  fof(f32,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f31])).
% 15.86/2.49  
% 15.86/2.49  fof(f71,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f32])).
% 15.86/2.49  
% 15.86/2.49  fof(f74,plain,(
% 15.86/2.49    v1_funct_1(sK4)),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f12,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f23,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f12])).
% 15.86/2.49  
% 15.86/2.49  fof(f24,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f23])).
% 15.86/2.49  
% 15.86/2.49  fof(f63,plain,(
% 15.86/2.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f24])).
% 15.86/2.49  
% 15.86/2.49  fof(f70,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f32])).
% 15.86/2.49  
% 15.86/2.49  fof(f69,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f32])).
% 15.86/2.49  
% 15.86/2.49  fof(f14,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f27,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f14])).
% 15.86/2.49  
% 15.86/2.49  fof(f28,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f27])).
% 15.86/2.49  
% 15.86/2.49  fof(f66,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f28])).
% 15.86/2.49  
% 15.86/2.49  fof(f13,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f25,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f13])).
% 15.86/2.49  
% 15.86/2.49  fof(f26,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f25])).
% 15.86/2.49  
% 15.86/2.49  fof(f65,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f26])).
% 15.86/2.49  
% 15.86/2.49  fof(f85,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(definition_unfolding,[],[f65,f79,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f75,plain,(
% 15.86/2.49    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f88,plain,(
% 15.86/2.49    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 15.86/2.49    inference(definition_unfolding,[],[f75,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f54,plain,(
% 15.86/2.49    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.86/2.49    inference(cnf_transformation,[],[f38])).
% 15.86/2.49  
% 15.86/2.49  fof(f80,plain,(
% 15.86/2.49    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 15.86/2.49    inference(definition_unfolding,[],[f54,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f15,axiom,(
% 15.86/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f29,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.86/2.49    inference(ennf_transformation,[],[f15])).
% 15.86/2.49  
% 15.86/2.49  fof(f30,plain,(
% 15.86/2.49    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.86/2.49    inference(flattening,[],[f29])).
% 15.86/2.49  
% 15.86/2.49  fof(f67,plain,(
% 15.86/2.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f30])).
% 15.86/2.49  
% 15.86/2.49  fof(f10,axiom,(
% 15.86/2.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f22,plain,(
% 15.86/2.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 15.86/2.49    inference(ennf_transformation,[],[f10])).
% 15.86/2.49  
% 15.86/2.49  fof(f60,plain,(
% 15.86/2.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f22])).
% 15.86/2.49  
% 15.86/2.49  fof(f84,plain,(
% 15.86/2.49    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.86/2.49    inference(definition_unfolding,[],[f60,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f11,axiom,(
% 15.86/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f41,plain,(
% 15.86/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.86/2.49    inference(nnf_transformation,[],[f11])).
% 15.86/2.49  
% 15.86/2.49  fof(f61,plain,(
% 15.86/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.86/2.49    inference(cnf_transformation,[],[f41])).
% 15.86/2.49  
% 15.86/2.49  fof(f3,axiom,(
% 15.86/2.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f19,plain,(
% 15.86/2.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.86/2.49    inference(ennf_transformation,[],[f3])).
% 15.86/2.49  
% 15.86/2.49  fof(f49,plain,(
% 15.86/2.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f19])).
% 15.86/2.49  
% 15.86/2.49  fof(f73,plain,(
% 15.86/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f89,plain,(
% 15.86/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 15.86/2.49    inference(definition_unfolding,[],[f73,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f72,plain,(
% 15.86/2.49    v1_funct_1(sK3)),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f77,plain,(
% 15.86/2.49    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)),
% 15.86/2.49    inference(cnf_transformation,[],[f44])).
% 15.86/2.49  
% 15.86/2.49  fof(f86,plain,(
% 15.86/2.49    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 15.86/2.49    inference(definition_unfolding,[],[f77,f79,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f9,axiom,(
% 15.86/2.49    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f21,plain,(
% 15.86/2.49    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 15.86/2.49    inference(ennf_transformation,[],[f9])).
% 15.86/2.49  
% 15.86/2.49  fof(f58,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 15.86/2.49    inference(cnf_transformation,[],[f21])).
% 15.86/2.49  
% 15.86/2.49  fof(f83,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 15.86/2.49    inference(definition_unfolding,[],[f58,f79])).
% 15.86/2.49  
% 15.86/2.49  fof(f8,axiom,(
% 15.86/2.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f39,plain,(
% 15.86/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.86/2.49    inference(nnf_transformation,[],[f8])).
% 15.86/2.49  
% 15.86/2.49  fof(f40,plain,(
% 15.86/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.86/2.49    inference(flattening,[],[f39])).
% 15.86/2.49  
% 15.86/2.49  fof(f56,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.86/2.49    inference(cnf_transformation,[],[f40])).
% 15.86/2.49  
% 15.86/2.49  fof(f93,plain,(
% 15.86/2.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.86/2.49    inference(equality_resolution,[],[f56])).
% 15.86/2.49  
% 15.86/2.49  fof(f1,axiom,(
% 15.86/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f35,plain,(
% 15.86/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.86/2.49    inference(nnf_transformation,[],[f1])).
% 15.86/2.49  
% 15.86/2.49  fof(f36,plain,(
% 15.86/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.86/2.49    inference(flattening,[],[f35])).
% 15.86/2.49  
% 15.86/2.49  fof(f47,plain,(
% 15.86/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f36])).
% 15.86/2.49  
% 15.86/2.49  fof(f57,plain,(
% 15.86/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.86/2.49    inference(cnf_transformation,[],[f40])).
% 15.86/2.49  
% 15.86/2.49  fof(f92,plain,(
% 15.86/2.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.86/2.49    inference(equality_resolution,[],[f57])).
% 15.86/2.49  
% 15.86/2.49  fof(f2,axiom,(
% 15.86/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.86/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.86/2.49  
% 15.86/2.49  fof(f48,plain,(
% 15.86/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f2])).
% 15.86/2.49  
% 15.86/2.49  fof(f45,plain,(
% 15.86/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.86/2.49    inference(cnf_transformation,[],[f36])).
% 15.86/2.49  
% 15.86/2.49  fof(f91,plain,(
% 15.86/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.86/2.49    inference(equality_resolution,[],[f45])).
% 15.86/2.49  
% 15.86/2.49  fof(f62,plain,(
% 15.86/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.86/2.49    inference(cnf_transformation,[],[f41])).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6,plain,
% 15.86/2.49      ( r2_hidden(sK0(X0,X1),X0)
% 15.86/2.49      | k2_enumset1(X1,X1,X1,X1) = X0
% 15.86/2.49      | k1_xboole_0 = X0 ),
% 15.86/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2435,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = X1
% 15.86/2.49      | k1_xboole_0 = X1
% 15.86/2.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_25,negated_conjecture,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 15.86/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2422,plain,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_21,plain,
% 15.86/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 15.86/2.49      | ~ v1_funct_1(X0) ),
% 15.86/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2425,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.86/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.86/2.49      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4161,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2425]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_27,negated_conjecture,
% 15.86/2.49      ( v1_funct_1(sK4) ),
% 15.86/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_32,plain,
% 15.86/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4478,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_4161,c_32,c_34,c_2964]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4479,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_4478]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4486,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_4479]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_16,plain,
% 15.86/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.86/2.49      | v1_partfun1(X0,X1)
% 15.86/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | k1_xboole_0 = X2 ),
% 15.86/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2430,plain,
% 15.86/2.49      ( k1_xboole_0 = X0
% 15.86/2.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 15.86/2.49      | v1_partfun1(X1,X2) = iProver_top
% 15.86/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.86/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6444,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_4486,c_2430]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_22,plain,
% 15.86/2.49      ( v1_funct_2(X0,X1,X2)
% 15.86/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 15.86/2.49      | ~ v1_funct_1(X3) ),
% 15.86/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2424,plain,
% 15.86/2.49      ( v1_funct_2(X0,X1,X2) = iProver_top
% 15.86/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
% 15.86/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3382,plain,
% 15.86/2.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2424]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3633,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_3382,c_32]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3634,plain,
% 15.86/2.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_3633]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4229,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_3634]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_23,plain,
% 15.86/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | v1_funct_1(X3) ),
% 15.86/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2423,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.86/2.49      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(X3) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2869,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2423]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3036,plain,
% 15.86/2.49      ( v1_funct_1(X0) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_2869,c_32]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3037,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_3036]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4230,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_3037]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13185,plain,
% 15.86/2.49      ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_6444,c_4229,c_4230]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13186,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_13185]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_18,plain,
% 15.86/2.49      ( ~ r1_partfun1(X0,X1)
% 15.86/2.49      | ~ v1_partfun1(X1,X2)
% 15.86/2.49      | ~ v1_partfun1(X0,X2)
% 15.86/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.86/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | ~ v1_funct_1(X1)
% 15.86/2.49      | X1 = X0 ),
% 15.86/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2428,plain,
% 15.86/2.49      ( X0 = X1
% 15.86/2.49      | r1_partfun1(X1,X0) != iProver_top
% 15.86/2.49      | v1_partfun1(X0,X2) != iProver_top
% 15.86/2.49      | v1_partfun1(X1,X2) != iProver_top
% 15.86/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.86/2.49      | v1_funct_1(X1) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6281,plain,
% 15.86/2.49      ( sK4 = X0
% 15.86/2.49      | r1_partfun1(X0,sK4) != iProver_top
% 15.86/2.49      | v1_partfun1(X0,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2428]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_17,plain,
% 15.86/2.49      ( r1_partfun1(X0,X1)
% 15.86/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 15.86/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | ~ v1_funct_1(X1) ),
% 15.86/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2429,plain,
% 15.86/2.49      ( r1_partfun1(X0,X1) = iProver_top
% 15.86/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6690,plain,
% 15.86/2.49      ( r1_partfun1(X0,sK4) = iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2429]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7596,plain,
% 15.86/2.49      ( v1_funct_1(X0) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(X0,sK1) != iProver_top
% 15.86/2.49      | sK4 = X0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_6281,c_32,c_34,c_3245]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7597,plain,
% 15.86/2.49      ( sK4 = X0
% 15.86/2.49      | v1_partfun1(X0,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_7596]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7611,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_4486,c_7597]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_10480,plain,
% 15.86/2.49      ( v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0) ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_7611,c_4230]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_10481,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0),sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_10480]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13196,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_13186,c_10481]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6442,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) = iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2430]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_26,negated_conjecture,
% 15.86/2.49      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 15.86/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_33,plain,
% 15.86/2.49      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_8367,plain,
% 15.86/2.49      ( v1_partfun1(sK4,sK1) = iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_6442,c_32,c_33]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_8368,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | v1_partfun1(sK4,sK1) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_8367]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13682,plain,
% 15.86/2.49      ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_13196,c_8368]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13683,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4),X0) = sK4 ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_13682]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = X1 | sK0(X1,X0) != X0 | k1_xboole_0 = X1 ),
% 15.86/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13692,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK4 != X0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_13683,c_5]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_15133,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
% 15.86/2.49      inference(equality_resolution,[status(thm)],[c_13692]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_15623,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_15133,c_4479]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_16548,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK4 = X0
% 15.86/2.49      | v1_partfun1(X0,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_15623,c_7597]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_15624,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_15133,c_3634]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_15625,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_15133,c_3037]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_16545,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 15.86/2.49      | v1_partfun1(X0,sK1) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_15623,c_2430]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_18474,plain,
% 15.86/2.49      ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.86/2.49      | sK4 = X0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_16548,c_7597,c_8368,c_15623,c_15624,c_15625,c_16545]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_18475,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK4 = X0
% 15.86/2.49      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_18474]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_18484,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_18475]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_20,plain,
% 15.86/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.86/2.49      | ~ r1_partfun1(X3,X0)
% 15.86/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 15.86/2.49      | ~ v1_funct_1(X3)
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | k1_xboole_0 = X2 ),
% 15.86/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2426,plain,
% 15.86/2.49      ( k1_xboole_0 = X0
% 15.86/2.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 15.86/2.49      | r1_partfun1(X3,X1) != iProver_top
% 15.86/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.86/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.86/2.49      | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
% 15.86/2.49      | v1_funct_1(X1) != iProver_top
% 15.86/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5155,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 15.86/2.49      | r1_partfun1(X0,sK4) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2426]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_34,plain,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3244,plain,
% 15.86/2.49      ( r1_partfun1(X0,sK4)
% 15.86/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 15.86/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 15.86/2.49      | ~ v1_funct_1(X0)
% 15.86/2.49      | ~ v1_funct_1(sK4) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3245,plain,
% 15.86/2.49      ( r1_partfun1(X0,sK4) = iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_3244]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5649,plain,
% 15.86/2.49      ( v1_funct_1(X0) != iProver_top
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_5155,c_32,c_33,c_34,c_3245]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5650,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_5649]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5661,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top
% 15.86/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_5650]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5728,plain,
% 15.86/2.49      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_5661,c_32]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5729,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_5728]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_19963,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4
% 15.86/2.49      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_18484,c_5729]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_12,plain,
% 15.86/2.49      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
% 15.86/2.49      | ~ r2_hidden(X0,X1) ),
% 15.86/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2434,plain,
% 15.86/2.49      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,X1) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_14,plain,
% 15.86/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.86/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2432,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.86/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3508,plain,
% 15.86/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.86/2.49      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2434,c_2432]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4,plain,
% 15.86/2.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.86/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2436,plain,
% 15.86/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3920,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 15.86/2.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_3508,c_2436]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_23717,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 15.86/2.49      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4 ),
% 15.86/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_19963,c_3920]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_28,negated_conjecture,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 15.86/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2419,plain,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4162,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2419,c_2425]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_29,negated_conjecture,
% 15.86/2.49      ( v1_funct_1(sK3) ),
% 15.86/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_30,plain,
% 15.86/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4651,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_4162,c_30,c_31,c_2979]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4652,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_4651]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4659,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_4652]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_6445,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_4659,c_2430]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3383,plain,
% 15.86/2.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2419,c_2424]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3804,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_3383,c_30]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3805,plain,
% 15.86/2.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_3804]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4231,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_3805]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2870,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top
% 15.86/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2419,c_2423]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3093,plain,
% 15.86/2.49      ( v1_funct_1(X0) = iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_2870,c_30]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3094,plain,
% 15.86/2.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_3093]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4232,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_3094]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_33443,plain,
% 15.86/2.49      ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_6445,c_4231,c_4232]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_33444,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_33443]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7612,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_4659,c_7597]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_10810,plain,
% 15.86/2.49      ( v1_partfun1(sK4,sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_7612,c_4232]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_10811,plain,
% 15.86/2.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_10810]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_33459,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 15.86/2.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_33444,c_10811]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_62354,plain,
% 15.86/2.49      ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_33459,c_8368]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_62355,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_62354]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_24,negated_conjecture,
% 15.86/2.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 15.86/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_62457,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_62355,c_24]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_64914,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = sK4
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_23717,c_62457]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_1820,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2688,plain,
% 15.86/2.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_1820]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2843,plain,
% 15.86/2.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_2688]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_1819,plain,( X0 = X0 ),theory(equality) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2844,plain,
% 15.86/2.49      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_1819]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_64919,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK4) = sK4 ),
% 15.86/2.49      inference(equality_resolution,[status(thm)],[c_62457]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_65242,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_64919,c_5]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_65565,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_64914,c_24,c_2843,c_2844,c_65242]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_65622,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_65565,c_3094]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_65623,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_65565,c_24]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5662,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 15.86/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2419,c_5650]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5792,plain,
% 15.86/2.49      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 15.86/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,[status(thm)],[c_5662,c_30]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5793,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_5792]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_65616,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_65565,c_5793]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67634,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_65616,c_3920]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67640,plain,
% 15.86/2.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_65622,c_65623,c_67634]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_11,plain,
% 15.86/2.49      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
% 15.86/2.49      | k1_xboole_0 = X1 ),
% 15.86/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_68609,plain,
% 15.86/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_67640,c_11]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_8,plain,
% 15.86/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.86/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_68733,plain,
% 15.86/2.49      ( k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 15.86/2.49      inference(light_normalisation,[status(thm)],[c_68609,c_8]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_68734,plain,
% 15.86/2.49      ( k1_xboole_0 = X0 ),
% 15.86/2.49      inference(equality_resolution_simp,[status(thm)],[c_68733]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3257,plain,
% 15.86/2.49      ( r1_tarski(sK4,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2422,c_2432]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_0,plain,
% 15.86/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.86/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2439,plain,
% 15.86/2.49      ( X0 = X1
% 15.86/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.86/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3546,plain,
% 15.86/2.49      ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
% 15.86/2.49      | r1_tarski(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK4) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_3257,c_2439]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67734,plain,
% 15.86/2.49      ( k2_zfmisc_1(sK1,k1_xboole_0) = sK4
% 15.86/2.49      | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK4) != iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67640,c_3546]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7,plain,
% 15.86/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.86/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67779,plain,
% 15.86/2.49      ( sK4 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67734,c_7]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3144,plain,
% 15.86/2.49      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3145,plain,
% 15.86/2.49      ( sK4 = X0
% 15.86/2.49      | r1_tarski(X0,sK4) != iProver_top
% 15.86/2.49      | r1_tarski(sK4,X0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_3144]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3147,plain,
% 15.86/2.49      ( sK4 = k1_xboole_0
% 15.86/2.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 15.86/2.49      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_3145]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3570,plain,
% 15.86/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 15.86/2.49      | r1_tarski(sK4,k1_xboole_0) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3571,plain,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_3570]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3,plain,
% 15.86/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 15.86/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3620,plain,
% 15.86/2.49      ( r1_tarski(k1_xboole_0,sK4) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3623,plain,
% 15.86/2.49      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_3620]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67741,plain,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67640,c_2422]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67753,plain,
% 15.86/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67741,c_7]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_70655,plain,
% 15.86/2.49      ( sK4 = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_67779,c_3147,c_3571,c_3623,c_67753]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2420,plain,
% 15.86/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_70672,plain,
% 15.86/2.49      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_70655,c_2420]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f91]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2438,plain,
% 15.86/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_13,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.86/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_2433,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.86/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4163,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) = iProver_top
% 15.86/2.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,X2)) != iProver_top
% 15.86/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_7,c_2425]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_4178,plain,
% 15.86/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.86/2.49      | r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X0)) != iProver_top
% 15.86/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_4163,c_7]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_5579,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | m1_subset_1(sK0(k5_partfun1(X1,k1_xboole_0,X2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.86/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2435,c_4178]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_22972,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | r1_tarski(sK0(k5_partfun1(X1,k1_xboole_0,X2),X0),k1_xboole_0) = iProver_top
% 15.86/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_5579,c_2432]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_23069,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(X1,k1_xboole_0,X2),X0) = k1_xboole_0
% 15.86/2.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_22972,c_2436]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_27740,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,X2)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,X2) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(X1,k1_xboole_0,X2),X0) = k1_xboole_0
% 15.86/2.49      | r1_tarski(X2,k1_xboole_0) != iProver_top
% 15.86/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2433,c_23069]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_27805,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0
% 15.86/2.49      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2438,c_27740]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_70987,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 15.86/2.49      | sK0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_70672,c_27805]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_71481,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 15.86/2.49      | k1_xboole_0 != X0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_70987,c_5]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_74178,plain,
% 15.86/2.49      ( k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 15.86/2.49      | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0) ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_71481,c_68734]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_74179,plain,
% 15.86/2.49      ( k2_enumset1(X0,X0,X0,X0) = k5_partfun1(X1,k1_xboole_0,k1_xboole_0)
% 15.86/2.49      | k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.86/2.49      inference(renaming,[status(thm)],[c_74178]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_74224,plain,
% 15.86/2.49      ( k5_partfun1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_74179,c_67640]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67744,plain,
% 15.86/2.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67640,c_24]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_70663,plain,
% 15.86/2.49      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_70655,c_67744]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3258,plain,
% 15.86/2.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_2419,c_2432]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3630,plain,
% 15.86/2.49      ( k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK3
% 15.86/2.49      | r1_tarski(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) != iProver_top ),
% 15.86/2.49      inference(superposition,[status(thm)],[c_3258,c_2439]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67733,plain,
% 15.86/2.49      ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
% 15.86/2.49      | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) != iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67640,c_3630]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67784,plain,
% 15.86/2.49      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67733,c_7]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3600,plain,
% 15.86/2.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3601,plain,
% 15.86/2.49      ( sK3 = X0
% 15.86/2.49      | r1_tarski(X0,sK3) != iProver_top
% 15.86/2.49      | r1_tarski(sK3,X0) != iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_3600]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_3603,plain,
% 15.86/2.49      ( sK3 = k1_xboole_0
% 15.86/2.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 15.86/2.49      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_3601]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7123,plain,
% 15.86/2.49      ( r1_tarski(k1_xboole_0,sK3) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_7126,plain,
% 15.86/2.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_7123]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_9241,plain,
% 15.86/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_9242,plain,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.86/2.49      | r1_tarski(sK3,X0) = iProver_top ),
% 15.86/2.49      inference(predicate_to_equality,[status(thm)],[c_9241]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_9244,plain,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.86/2.49      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 15.86/2.49      inference(instantiation,[status(thm)],[c_9242]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67742,plain,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67640,c_2419]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_67750,plain,
% 15.86/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_67742,c_7]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_70719,plain,
% 15.86/2.49      ( sK3 = k1_xboole_0 ),
% 15.86/2.49      inference(global_propositional_subsumption,
% 15.86/2.49                [status(thm)],
% 15.86/2.49                [c_67784,c_3603,c_7126,c_9244,c_67750]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_71191,plain,
% 15.86/2.49      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK1,k1_xboole_0,k1_xboole_0) ),
% 15.86/2.49      inference(light_normalisation,[status(thm)],[c_70663,c_70719]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_75560,plain,
% 15.86/2.49      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_74224,c_71191]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_77408,plain,
% 15.86/2.49      ( k1_xboole_0 != k1_xboole_0 ),
% 15.86/2.49      inference(demodulation,[status(thm)],[c_68734,c_75560]) ).
% 15.86/2.49  
% 15.86/2.49  cnf(c_77544,plain,
% 15.86/2.49      ( $false ),
% 15.86/2.49      inference(equality_resolution_simp,[status(thm)],[c_77408]) ).
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.86/2.49  
% 15.86/2.49  ------                               Statistics
% 15.86/2.49  
% 15.86/2.49  ------ General
% 15.86/2.49  
% 15.86/2.49  abstr_ref_over_cycles:                  0
% 15.86/2.49  abstr_ref_under_cycles:                 0
% 15.86/2.49  gc_basic_clause_elim:                   0
% 15.86/2.49  forced_gc_time:                         0
% 15.86/2.49  parsing_time:                           0.01
% 15.86/2.49  unif_index_cands_time:                  0.
% 15.86/2.49  unif_index_add_time:                    0.
% 15.86/2.49  orderings_time:                         0.
% 15.86/2.49  out_proof_time:                         0.024
% 15.86/2.49  total_time:                             1.994
% 15.86/2.49  num_of_symbols:                         48
% 15.86/2.49  num_of_terms:                           31638
% 15.86/2.49  
% 15.86/2.49  ------ Preprocessing
% 15.86/2.49  
% 15.86/2.49  num_of_splits:                          0
% 15.86/2.49  num_of_split_atoms:                     0
% 15.86/2.49  num_of_reused_defs:                     0
% 15.86/2.49  num_eq_ax_congr_red:                    15
% 15.86/2.49  num_of_sem_filtered_clauses:            1
% 15.86/2.49  num_of_subtypes:                        0
% 15.86/2.49  monotx_restored_types:                  0
% 15.86/2.49  sat_num_of_epr_types:                   0
% 15.86/2.49  sat_num_of_non_cyclic_types:            0
% 15.86/2.49  sat_guarded_non_collapsed_types:        0
% 15.86/2.49  num_pure_diseq_elim:                    0
% 15.86/2.49  simp_replaced_by:                       0
% 15.86/2.49  res_preprocessed:                       141
% 15.86/2.49  prep_upred:                             0
% 15.86/2.49  prep_unflattend:                        74
% 15.86/2.49  smt_new_axioms:                         0
% 15.86/2.49  pred_elim_cands:                        7
% 15.86/2.49  pred_elim:                              0
% 15.86/2.49  pred_elim_cl:                           0
% 15.86/2.49  pred_elim_cycles:                       6
% 15.86/2.49  merged_defs:                            8
% 15.86/2.49  merged_defs_ncl:                        0
% 15.86/2.49  bin_hyper_res:                          8
% 15.86/2.49  prep_cycles:                            4
% 15.86/2.49  pred_elim_time:                         0.028
% 15.86/2.49  splitting_time:                         0.
% 15.86/2.49  sem_filter_time:                        0.
% 15.86/2.49  monotx_time:                            0.001
% 15.86/2.49  subtype_inf_time:                       0.
% 15.86/2.49  
% 15.86/2.49  ------ Problem properties
% 15.86/2.49  
% 15.86/2.49  clauses:                                29
% 15.86/2.49  conjectures:                            6
% 15.86/2.49  epr:                                    6
% 15.86/2.49  horn:                                   24
% 15.86/2.49  ground:                                 6
% 15.86/2.49  unary:                                  10
% 15.86/2.49  binary:                                 6
% 15.86/2.49  lits:                                   83
% 15.86/2.49  lits_eq:                                20
% 15.86/2.49  fd_pure:                                0
% 15.86/2.49  fd_pseudo:                              0
% 15.86/2.49  fd_cond:                                6
% 15.86/2.49  fd_pseudo_cond:                         4
% 15.86/2.49  ac_symbols:                             0
% 15.86/2.49  
% 15.86/2.49  ------ Propositional Solver
% 15.86/2.49  
% 15.86/2.49  prop_solver_calls:                      33
% 15.86/2.49  prop_fast_solver_calls:                 5001
% 15.86/2.49  smt_solver_calls:                       0
% 15.86/2.49  smt_fast_solver_calls:                  0
% 15.86/2.49  prop_num_of_clauses:                    17076
% 15.86/2.49  prop_preprocess_simplified:             23534
% 15.86/2.49  prop_fo_subsumed:                       345
% 15.86/2.49  prop_solver_time:                       0.
% 15.86/2.49  smt_solver_time:                        0.
% 15.86/2.49  smt_fast_solver_time:                   0.
% 15.86/2.49  prop_fast_solver_time:                  0.
% 15.86/2.49  prop_unsat_core_time:                   0.
% 15.86/2.49  
% 15.86/2.49  ------ QBF
% 15.86/2.49  
% 15.86/2.49  qbf_q_res:                              0
% 15.86/2.49  qbf_num_tautologies:                    0
% 15.86/2.49  qbf_prep_cycles:                        0
% 15.86/2.49  
% 15.86/2.49  ------ BMC1
% 15.86/2.49  
% 15.86/2.49  bmc1_current_bound:                     -1
% 15.86/2.49  bmc1_last_solved_bound:                 -1
% 15.86/2.49  bmc1_unsat_core_size:                   -1
% 15.86/2.49  bmc1_unsat_core_parents_size:           -1
% 15.86/2.49  bmc1_merge_next_fun:                    0
% 15.86/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.86/2.49  
% 15.86/2.49  ------ Instantiation
% 15.86/2.49  
% 15.86/2.49  inst_num_of_clauses:                    3789
% 15.86/2.49  inst_num_in_passive:                    956
% 15.86/2.49  inst_num_in_active:                     1994
% 15.86/2.49  inst_num_in_unprocessed:                840
% 15.86/2.49  inst_num_of_loops:                      2410
% 15.86/2.49  inst_num_of_learning_restarts:          0
% 15.86/2.49  inst_num_moves_active_passive:          412
% 15.86/2.49  inst_lit_activity:                      0
% 15.86/2.49  inst_lit_activity_moves:                0
% 15.86/2.49  inst_num_tautologies:                   0
% 15.86/2.49  inst_num_prop_implied:                  0
% 15.86/2.49  inst_num_existing_simplified:           0
% 15.86/2.49  inst_num_eq_res_simplified:             0
% 15.86/2.49  inst_num_child_elim:                    0
% 15.86/2.49  inst_num_of_dismatching_blockings:      2743
% 15.86/2.49  inst_num_of_non_proper_insts:           7717
% 15.86/2.49  inst_num_of_duplicates:                 0
% 15.86/2.49  inst_inst_num_from_inst_to_res:         0
% 15.86/2.49  inst_dismatching_checking_time:         0.
% 15.86/2.49  
% 15.86/2.49  ------ Resolution
% 15.86/2.49  
% 15.86/2.49  res_num_of_clauses:                     0
% 15.86/2.49  res_num_in_passive:                     0
% 15.86/2.49  res_num_in_active:                      0
% 15.86/2.49  res_num_of_loops:                       145
% 15.86/2.49  res_forward_subset_subsumed:            449
% 15.86/2.49  res_backward_subset_subsumed:           6
% 15.86/2.49  res_forward_subsumed:                   0
% 15.86/2.49  res_backward_subsumed:                  0
% 15.86/2.49  res_forward_subsumption_resolution:     10
% 15.86/2.49  res_backward_subsumption_resolution:    0
% 15.86/2.49  res_clause_to_clause_subsumption:       10579
% 15.86/2.49  res_orphan_elimination:                 0
% 15.86/2.49  res_tautology_del:                      634
% 15.86/2.49  res_num_eq_res_simplified:              0
% 15.86/2.49  res_num_sel_changes:                    0
% 15.86/2.49  res_moves_from_active_to_pass:          0
% 15.86/2.49  
% 15.86/2.49  ------ Superposition
% 15.86/2.49  
% 15.86/2.49  sup_time_total:                         0.
% 15.86/2.49  sup_time_generating:                    0.
% 15.86/2.49  sup_time_sim_full:                      0.
% 15.86/2.49  sup_time_sim_immed:                     0.
% 15.86/2.49  
% 15.86/2.49  sup_num_of_clauses:                     390
% 15.86/2.49  sup_num_in_active:                      18
% 15.86/2.49  sup_num_in_passive:                     372
% 15.86/2.49  sup_num_of_loops:                       480
% 15.86/2.49  sup_fw_superposition:                   1836
% 15.86/2.49  sup_bw_superposition:                   2189
% 15.86/2.49  sup_immediate_simplified:               1430
% 15.86/2.49  sup_given_eliminated:                   2
% 15.86/2.49  comparisons_done:                       0
% 15.86/2.49  comparisons_avoided:                    571
% 15.86/2.49  
% 15.86/2.49  ------ Simplifications
% 15.86/2.49  
% 15.86/2.49  
% 15.86/2.49  sim_fw_subset_subsumed:                 553
% 15.86/2.49  sim_bw_subset_subsumed:                 1227
% 15.86/2.49  sim_fw_subsumed:                        514
% 15.86/2.49  sim_bw_subsumed:                        215
% 15.86/2.49  sim_fw_subsumption_res:                 12
% 15.86/2.49  sim_bw_subsumption_res:                 14
% 15.86/2.49  sim_tautology_del:                      172
% 15.86/2.49  sim_eq_tautology_del:                   135
% 15.86/2.49  sim_eq_res_simp:                        1
% 15.86/2.49  sim_fw_demodulated:                     176
% 15.86/2.49  sim_bw_demodulated:                     243
% 15.86/2.49  sim_light_normalised:                   129
% 15.86/2.49  sim_joinable_taut:                      0
% 15.86/2.49  sim_joinable_simp:                      0
% 15.86/2.49  sim_ac_normalised:                      0
% 15.86/2.49  sim_smt_subsumption:                    0
% 15.86/2.49  
%------------------------------------------------------------------------------
