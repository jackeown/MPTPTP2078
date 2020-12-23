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
% DateTime   : Thu Dec  3 12:08:53 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_27)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38,f37])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f56,f70,f70])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f11,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f68,plain,(
    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f68,f70,f70])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f86,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X3))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f70,f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f70,f70])).

fof(f87,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f78])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1034,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1015,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2405,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_1021])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2550,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2405,c_26,c_27,c_2131])).

cnf(c_2551,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2550])).

cnf(c_2556,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_2551])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1026,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3875,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2556,c_1026])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1019,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1402,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_1019])).

cnf(c_1596,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1402,c_26])).

cnf(c_1597,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1596])).

cnf(c_1910,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1597])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1020,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1895,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_1020])).

cnf(c_2139,plain,
    ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1895,c_26])).

cnf(c_2140,plain,
    ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2139])).

cnf(c_2145,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_2140])).

cnf(c_6694,plain,
    ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_1910,c_2145])).

cnf(c_6695,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_6694])).

cnf(c_13,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1025,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3890,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2556,c_1025])).

cnf(c_6005,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3890,c_1910])).

cnf(c_6006,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6005])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1018,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1024,plain,
    ( X0 = X1
    | r1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3660,plain,
    ( sK4 = X0
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1024])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4547,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3660,c_28])).

cnf(c_4548,plain,
    ( sK4 = X0
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(X0,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4547])).

cnf(c_4556,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2556,c_4548])).

cnf(c_5893,plain,
    ( v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4556,c_1910])).

cnf(c_5894,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5893])).

cnf(c_6011,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6006,c_5894])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6601,plain,
    ( v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6011,c_28,c_30])).

cnf(c_6602,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6601])).

cnf(c_6701,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | v1_partfun1(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6695,c_6602])).

cnf(c_3872,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_partfun1(sK4,sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1026])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,plain,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4933,plain,
    ( v1_partfun1(sK4,sK1) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3872,c_28,c_29])).

cnf(c_4934,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_partfun1(sK4,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4933])).

cnf(c_16336,plain,
    ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6701,c_4934])).

cnf(c_16337,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(renaming,[status(thm)],[c_16336])).

cnf(c_20,negated_conjecture,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_16404,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
    inference(superposition,[status(thm)],[c_16337,c_20])).

cnf(c_631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1083,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1121,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_630,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16346,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | sK4 != X0 ),
    inference(superposition,[status(thm)],[c_16337,c_0])).

cnf(c_16576,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_16346])).

cnf(c_16776,plain,
    ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16404,c_20,c_1121,c_1145,c_16576])).

cnf(c_16777,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_16776])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1022,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2923,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1022])).

cnf(c_2360,plain,
    ( r1_partfun1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2361,plain,
    ( r1_partfun1(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_3236,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_28,c_29,c_30,c_2361])).

cnf(c_3237,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3236])).

cnf(c_3243,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_3237])).

cnf(c_3410,plain,
    ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3243,c_26])).

cnf(c_3411,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3410])).

cnf(c_16794,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16777,c_3411])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1033,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1859,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1033])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
    | X3 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1032,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1636,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1032])).

cnf(c_1867,plain,
    ( X0 = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_1636])).

cnf(c_16947,plain,
    ( X0 = X1
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16794,c_1867])).

cnf(c_17526,plain,
    ( X0 = X1
    | k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_16947,c_20])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1029,plain,
    ( X0 = X1
    | r1_xboole_0(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1972,plain,
    ( X0 = X1
    | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1029])).

cnf(c_1977,plain,
    ( X0 = X1
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1972])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1028,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17434,plain,
    ( X0 = X1
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16947,c_1028])).

cnf(c_19525,plain,
    ( X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17526,c_1977,c_17434])).

cnf(c_19744,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0 ),
    inference(superposition,[status(thm)],[c_19525,c_20])).

cnf(c_19897,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_19744])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  ------ Input Options
% 7.78/1.48  
% 7.78/1.48  --out_options                           all
% 7.78/1.48  --tptp_safe_out                         true
% 7.78/1.48  --problem_path                          ""
% 7.78/1.48  --include_path                          ""
% 7.78/1.48  --clausifier                            res/vclausify_rel
% 7.78/1.48  --clausifier_options                    ""
% 7.78/1.48  --stdin                                 false
% 7.78/1.48  --stats_out                             all
% 7.78/1.48  
% 7.78/1.48  ------ General Options
% 7.78/1.48  
% 7.78/1.48  --fof                                   false
% 7.78/1.48  --time_out_real                         305.
% 7.78/1.48  --time_out_virtual                      -1.
% 7.78/1.48  --symbol_type_check                     false
% 7.78/1.48  --clausify_out                          false
% 7.78/1.48  --sig_cnt_out                           false
% 7.78/1.48  --trig_cnt_out                          false
% 7.78/1.48  --trig_cnt_out_tolerance                1.
% 7.78/1.48  --trig_cnt_out_sk_spl                   false
% 7.78/1.48  --abstr_cl_out                          false
% 7.78/1.48  
% 7.78/1.48  ------ Global Options
% 7.78/1.48  
% 7.78/1.48  --schedule                              default
% 7.78/1.48  --add_important_lit                     false
% 7.78/1.48  --prop_solver_per_cl                    1000
% 7.78/1.48  --min_unsat_core                        false
% 7.78/1.48  --soft_assumptions                      false
% 7.78/1.48  --soft_lemma_size                       3
% 7.78/1.48  --prop_impl_unit_size                   0
% 7.78/1.48  --prop_impl_unit                        []
% 7.78/1.48  --share_sel_clauses                     true
% 7.78/1.48  --reset_solvers                         false
% 7.78/1.48  --bc_imp_inh                            [conj_cone]
% 7.78/1.48  --conj_cone_tolerance                   3.
% 7.78/1.48  --extra_neg_conj                        none
% 7.78/1.48  --large_theory_mode                     true
% 7.78/1.48  --prolific_symb_bound                   200
% 7.78/1.48  --lt_threshold                          2000
% 7.78/1.48  --clause_weak_htbl                      true
% 7.78/1.48  --gc_record_bc_elim                     false
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing Options
% 7.78/1.48  
% 7.78/1.48  --preprocessing_flag                    true
% 7.78/1.48  --time_out_prep_mult                    0.1
% 7.78/1.48  --splitting_mode                        input
% 7.78/1.48  --splitting_grd                         true
% 7.78/1.48  --splitting_cvd                         false
% 7.78/1.48  --splitting_cvd_svl                     false
% 7.78/1.48  --splitting_nvd                         32
% 7.78/1.48  --sub_typing                            true
% 7.78/1.48  --prep_gs_sim                           true
% 7.78/1.48  --prep_unflatten                        true
% 7.78/1.48  --prep_res_sim                          true
% 7.78/1.48  --prep_upred                            true
% 7.78/1.48  --prep_sem_filter                       exhaustive
% 7.78/1.48  --prep_sem_filter_out                   false
% 7.78/1.48  --pred_elim                             true
% 7.78/1.48  --res_sim_input                         true
% 7.78/1.48  --eq_ax_congr_red                       true
% 7.78/1.48  --pure_diseq_elim                       true
% 7.78/1.48  --brand_transform                       false
% 7.78/1.48  --non_eq_to_eq                          false
% 7.78/1.48  --prep_def_merge                        true
% 7.78/1.48  --prep_def_merge_prop_impl              false
% 7.78/1.48  --prep_def_merge_mbd                    true
% 7.78/1.48  --prep_def_merge_tr_red                 false
% 7.78/1.48  --prep_def_merge_tr_cl                  false
% 7.78/1.48  --smt_preprocessing                     true
% 7.78/1.48  --smt_ac_axioms                         fast
% 7.78/1.48  --preprocessed_out                      false
% 7.78/1.48  --preprocessed_stats                    false
% 7.78/1.48  
% 7.78/1.48  ------ Abstraction refinement Options
% 7.78/1.48  
% 7.78/1.48  --abstr_ref                             []
% 7.78/1.48  --abstr_ref_prep                        false
% 7.78/1.48  --abstr_ref_until_sat                   false
% 7.78/1.48  --abstr_ref_sig_restrict                funpre
% 7.78/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.48  --abstr_ref_under                       []
% 7.78/1.48  
% 7.78/1.48  ------ SAT Options
% 7.78/1.48  
% 7.78/1.48  --sat_mode                              false
% 7.78/1.48  --sat_fm_restart_options                ""
% 7.78/1.48  --sat_gr_def                            false
% 7.78/1.48  --sat_epr_types                         true
% 7.78/1.48  --sat_non_cyclic_types                  false
% 7.78/1.48  --sat_finite_models                     false
% 7.78/1.48  --sat_fm_lemmas                         false
% 7.78/1.48  --sat_fm_prep                           false
% 7.78/1.48  --sat_fm_uc_incr                        true
% 7.78/1.48  --sat_out_model                         small
% 7.78/1.48  --sat_out_clauses                       false
% 7.78/1.48  
% 7.78/1.48  ------ QBF Options
% 7.78/1.48  
% 7.78/1.48  --qbf_mode                              false
% 7.78/1.48  --qbf_elim_univ                         false
% 7.78/1.48  --qbf_dom_inst                          none
% 7.78/1.48  --qbf_dom_pre_inst                      false
% 7.78/1.48  --qbf_sk_in                             false
% 7.78/1.48  --qbf_pred_elim                         true
% 7.78/1.48  --qbf_split                             512
% 7.78/1.48  
% 7.78/1.48  ------ BMC1 Options
% 7.78/1.48  
% 7.78/1.48  --bmc1_incremental                      false
% 7.78/1.48  --bmc1_axioms                           reachable_all
% 7.78/1.48  --bmc1_min_bound                        0
% 7.78/1.48  --bmc1_max_bound                        -1
% 7.78/1.48  --bmc1_max_bound_default                -1
% 7.78/1.48  --bmc1_symbol_reachability              true
% 7.78/1.48  --bmc1_property_lemmas                  false
% 7.78/1.48  --bmc1_k_induction                      false
% 7.78/1.48  --bmc1_non_equiv_states                 false
% 7.78/1.48  --bmc1_deadlock                         false
% 7.78/1.48  --bmc1_ucm                              false
% 7.78/1.48  --bmc1_add_unsat_core                   none
% 7.78/1.48  --bmc1_unsat_core_children              false
% 7.78/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.48  --bmc1_out_stat                         full
% 7.78/1.48  --bmc1_ground_init                      false
% 7.78/1.48  --bmc1_pre_inst_next_state              false
% 7.78/1.48  --bmc1_pre_inst_state                   false
% 7.78/1.48  --bmc1_pre_inst_reach_state             false
% 7.78/1.48  --bmc1_out_unsat_core                   false
% 7.78/1.48  --bmc1_aig_witness_out                  false
% 7.78/1.48  --bmc1_verbose                          false
% 7.78/1.48  --bmc1_dump_clauses_tptp                false
% 7.78/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.48  --bmc1_dump_file                        -
% 7.78/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.48  --bmc1_ucm_extend_mode                  1
% 7.78/1.48  --bmc1_ucm_init_mode                    2
% 7.78/1.48  --bmc1_ucm_cone_mode                    none
% 7.78/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.48  --bmc1_ucm_relax_model                  4
% 7.78/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.48  --bmc1_ucm_layered_model                none
% 7.78/1.48  --bmc1_ucm_max_lemma_size               10
% 7.78/1.48  
% 7.78/1.48  ------ AIG Options
% 7.78/1.48  
% 7.78/1.48  --aig_mode                              false
% 7.78/1.48  
% 7.78/1.48  ------ Instantiation Options
% 7.78/1.48  
% 7.78/1.48  --instantiation_flag                    true
% 7.78/1.48  --inst_sos_flag                         true
% 7.78/1.48  --inst_sos_phase                        true
% 7.78/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel_side                     num_symb
% 7.78/1.48  --inst_solver_per_active                1400
% 7.78/1.48  --inst_solver_calls_frac                1.
% 7.78/1.48  --inst_passive_queue_type               priority_queues
% 7.78/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.48  --inst_passive_queues_freq              [25;2]
% 7.78/1.48  --inst_dismatching                      true
% 7.78/1.48  --inst_eager_unprocessed_to_passive     true
% 7.78/1.48  --inst_prop_sim_given                   true
% 7.78/1.48  --inst_prop_sim_new                     false
% 7.78/1.48  --inst_subs_new                         false
% 7.78/1.48  --inst_eq_res_simp                      false
% 7.78/1.48  --inst_subs_given                       false
% 7.78/1.48  --inst_orphan_elimination               true
% 7.78/1.48  --inst_learning_loop_flag               true
% 7.78/1.48  --inst_learning_start                   3000
% 7.78/1.48  --inst_learning_factor                  2
% 7.78/1.48  --inst_start_prop_sim_after_learn       3
% 7.78/1.48  --inst_sel_renew                        solver
% 7.78/1.48  --inst_lit_activity_flag                true
% 7.78/1.48  --inst_restr_to_given                   false
% 7.78/1.48  --inst_activity_threshold               500
% 7.78/1.48  --inst_out_proof                        true
% 7.78/1.48  
% 7.78/1.48  ------ Resolution Options
% 7.78/1.48  
% 7.78/1.48  --resolution_flag                       true
% 7.78/1.48  --res_lit_sel                           adaptive
% 7.78/1.48  --res_lit_sel_side                      none
% 7.78/1.48  --res_ordering                          kbo
% 7.78/1.48  --res_to_prop_solver                    active
% 7.78/1.48  --res_prop_simpl_new                    false
% 7.78/1.48  --res_prop_simpl_given                  true
% 7.78/1.48  --res_passive_queue_type                priority_queues
% 7.78/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.48  --res_passive_queues_freq               [15;5]
% 7.78/1.48  --res_forward_subs                      full
% 7.78/1.48  --res_backward_subs                     full
% 7.78/1.48  --res_forward_subs_resolution           true
% 7.78/1.48  --res_backward_subs_resolution          true
% 7.78/1.48  --res_orphan_elimination                true
% 7.78/1.48  --res_time_limit                        2.
% 7.78/1.48  --res_out_proof                         true
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Options
% 7.78/1.48  
% 7.78/1.48  --superposition_flag                    true
% 7.78/1.48  --sup_passive_queue_type                priority_queues
% 7.78/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.48  --demod_completeness_check              fast
% 7.78/1.48  --demod_use_ground                      true
% 7.78/1.48  --sup_to_prop_solver                    passive
% 7.78/1.48  --sup_prop_simpl_new                    true
% 7.78/1.48  --sup_prop_simpl_given                  true
% 7.78/1.48  --sup_fun_splitting                     true
% 7.78/1.48  --sup_smt_interval                      50000
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Simplification Setup
% 7.78/1.48  
% 7.78/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_immed_triv                        [TrivRules]
% 7.78/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_bw_main                     []
% 7.78/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_input_bw                          []
% 7.78/1.48  
% 7.78/1.48  ------ Combination Options
% 7.78/1.48  
% 7.78/1.48  --comb_res_mult                         3
% 7.78/1.48  --comb_sup_mult                         2
% 7.78/1.48  --comb_inst_mult                        10
% 7.78/1.48  
% 7.78/1.48  ------ Debug Options
% 7.78/1.48  
% 7.78/1.48  --dbg_backtrace                         false
% 7.78/1.48  --dbg_dump_prop_clauses                 false
% 7.78/1.48  --dbg_dump_prop_clauses_file            -
% 7.78/1.48  --dbg_out_stat                          false
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 26
% 7.78/1.48  conjectures                             6
% 7.78/1.48  EPR                                     2
% 7.78/1.48  Horn                                    19
% 7.78/1.48  unary                                   9
% 7.78/1.48  binary                                  5
% 7.78/1.49  lits                                    77
% 7.78/1.49  lits eq                                 17
% 7.78/1.49  fd_pure                                 0
% 7.78/1.49  fd_pseudo                               0
% 7.78/1.49  fd_cond                                 3
% 7.78/1.49  fd_pseudo_cond                          6
% 7.78/1.49  AC symbols                              0
% 7.78/1.49  
% 7.78/1.49  ------ Schedule dynamic 5 is on 
% 7.78/1.49  
% 7.78/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ 
% 7.78/1.49  Current options:
% 7.78/1.49  ------ 
% 7.78/1.49  
% 7.78/1.49  ------ Input Options
% 7.78/1.49  
% 7.78/1.49  --out_options                           all
% 7.78/1.49  --tptp_safe_out                         true
% 7.78/1.49  --problem_path                          ""
% 7.78/1.49  --include_path                          ""
% 7.78/1.49  --clausifier                            res/vclausify_rel
% 7.78/1.49  --clausifier_options                    ""
% 7.78/1.49  --stdin                                 false
% 7.78/1.49  --stats_out                             all
% 7.78/1.49  
% 7.78/1.49  ------ General Options
% 7.78/1.49  
% 7.78/1.49  --fof                                   false
% 7.78/1.49  --time_out_real                         305.
% 7.78/1.49  --time_out_virtual                      -1.
% 7.78/1.49  --symbol_type_check                     false
% 7.78/1.49  --clausify_out                          false
% 7.78/1.49  --sig_cnt_out                           false
% 7.78/1.49  --trig_cnt_out                          false
% 7.78/1.49  --trig_cnt_out_tolerance                1.
% 7.78/1.49  --trig_cnt_out_sk_spl                   false
% 7.78/1.49  --abstr_cl_out                          false
% 7.78/1.49  
% 7.78/1.49  ------ Global Options
% 7.78/1.49  
% 7.78/1.49  --schedule                              default
% 7.78/1.49  --add_important_lit                     false
% 7.78/1.49  --prop_solver_per_cl                    1000
% 7.78/1.49  --min_unsat_core                        false
% 7.78/1.49  --soft_assumptions                      false
% 7.78/1.49  --soft_lemma_size                       3
% 7.78/1.49  --prop_impl_unit_size                   0
% 7.78/1.49  --prop_impl_unit                        []
% 7.78/1.49  --share_sel_clauses                     true
% 7.78/1.49  --reset_solvers                         false
% 7.78/1.49  --bc_imp_inh                            [conj_cone]
% 7.78/1.49  --conj_cone_tolerance                   3.
% 7.78/1.49  --extra_neg_conj                        none
% 7.78/1.49  --large_theory_mode                     true
% 7.78/1.49  --prolific_symb_bound                   200
% 7.78/1.49  --lt_threshold                          2000
% 7.78/1.49  --clause_weak_htbl                      true
% 7.78/1.49  --gc_record_bc_elim                     false
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing Options
% 7.78/1.49  
% 7.78/1.49  --preprocessing_flag                    true
% 7.78/1.49  --time_out_prep_mult                    0.1
% 7.78/1.49  --splitting_mode                        input
% 7.78/1.49  --splitting_grd                         true
% 7.78/1.49  --splitting_cvd                         false
% 7.78/1.49  --splitting_cvd_svl                     false
% 7.78/1.49  --splitting_nvd                         32
% 7.78/1.49  --sub_typing                            true
% 7.78/1.49  --prep_gs_sim                           true
% 7.78/1.49  --prep_unflatten                        true
% 7.78/1.49  --prep_res_sim                          true
% 7.78/1.49  --prep_upred                            true
% 7.78/1.49  --prep_sem_filter                       exhaustive
% 7.78/1.49  --prep_sem_filter_out                   false
% 7.78/1.49  --pred_elim                             true
% 7.78/1.49  --res_sim_input                         true
% 7.78/1.49  --eq_ax_congr_red                       true
% 7.78/1.49  --pure_diseq_elim                       true
% 7.78/1.49  --brand_transform                       false
% 7.78/1.49  --non_eq_to_eq                          false
% 7.78/1.49  --prep_def_merge                        true
% 7.78/1.49  --prep_def_merge_prop_impl              false
% 7.78/1.49  --prep_def_merge_mbd                    true
% 7.78/1.49  --prep_def_merge_tr_red                 false
% 7.78/1.49  --prep_def_merge_tr_cl                  false
% 7.78/1.49  --smt_preprocessing                     true
% 7.78/1.49  --smt_ac_axioms                         fast
% 7.78/1.49  --preprocessed_out                      false
% 7.78/1.49  --preprocessed_stats                    false
% 7.78/1.49  
% 7.78/1.49  ------ Abstraction refinement Options
% 7.78/1.49  
% 7.78/1.49  --abstr_ref                             []
% 7.78/1.49  --abstr_ref_prep                        false
% 7.78/1.49  --abstr_ref_until_sat                   false
% 7.78/1.49  --abstr_ref_sig_restrict                funpre
% 7.78/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.49  --abstr_ref_under                       []
% 7.78/1.49  
% 7.78/1.49  ------ SAT Options
% 7.78/1.49  
% 7.78/1.49  --sat_mode                              false
% 7.78/1.49  --sat_fm_restart_options                ""
% 7.78/1.49  --sat_gr_def                            false
% 7.78/1.49  --sat_epr_types                         true
% 7.78/1.49  --sat_non_cyclic_types                  false
% 7.78/1.49  --sat_finite_models                     false
% 7.78/1.49  --sat_fm_lemmas                         false
% 7.78/1.49  --sat_fm_prep                           false
% 7.78/1.49  --sat_fm_uc_incr                        true
% 7.78/1.49  --sat_out_model                         small
% 7.78/1.49  --sat_out_clauses                       false
% 7.78/1.49  
% 7.78/1.49  ------ QBF Options
% 7.78/1.49  
% 7.78/1.49  --qbf_mode                              false
% 7.78/1.49  --qbf_elim_univ                         false
% 7.78/1.49  --qbf_dom_inst                          none
% 7.78/1.49  --qbf_dom_pre_inst                      false
% 7.78/1.49  --qbf_sk_in                             false
% 7.78/1.49  --qbf_pred_elim                         true
% 7.78/1.49  --qbf_split                             512
% 7.78/1.49  
% 7.78/1.49  ------ BMC1 Options
% 7.78/1.49  
% 7.78/1.49  --bmc1_incremental                      false
% 7.78/1.49  --bmc1_axioms                           reachable_all
% 7.78/1.49  --bmc1_min_bound                        0
% 7.78/1.49  --bmc1_max_bound                        -1
% 7.78/1.49  --bmc1_max_bound_default                -1
% 7.78/1.49  --bmc1_symbol_reachability              true
% 7.78/1.49  --bmc1_property_lemmas                  false
% 7.78/1.49  --bmc1_k_induction                      false
% 7.78/1.49  --bmc1_non_equiv_states                 false
% 7.78/1.49  --bmc1_deadlock                         false
% 7.78/1.49  --bmc1_ucm                              false
% 7.78/1.49  --bmc1_add_unsat_core                   none
% 7.78/1.49  --bmc1_unsat_core_children              false
% 7.78/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.49  --bmc1_out_stat                         full
% 7.78/1.49  --bmc1_ground_init                      false
% 7.78/1.49  --bmc1_pre_inst_next_state              false
% 7.78/1.49  --bmc1_pre_inst_state                   false
% 7.78/1.49  --bmc1_pre_inst_reach_state             false
% 7.78/1.49  --bmc1_out_unsat_core                   false
% 7.78/1.49  --bmc1_aig_witness_out                  false
% 7.78/1.49  --bmc1_verbose                          false
% 7.78/1.49  --bmc1_dump_clauses_tptp                false
% 7.78/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.49  --bmc1_dump_file                        -
% 7.78/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.49  --bmc1_ucm_extend_mode                  1
% 7.78/1.49  --bmc1_ucm_init_mode                    2
% 7.78/1.49  --bmc1_ucm_cone_mode                    none
% 7.78/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.49  --bmc1_ucm_relax_model                  4
% 7.78/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.49  --bmc1_ucm_layered_model                none
% 7.78/1.49  --bmc1_ucm_max_lemma_size               10
% 7.78/1.49  
% 7.78/1.49  ------ AIG Options
% 7.78/1.49  
% 7.78/1.49  --aig_mode                              false
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation Options
% 7.78/1.49  
% 7.78/1.49  --instantiation_flag                    true
% 7.78/1.49  --inst_sos_flag                         true
% 7.78/1.49  --inst_sos_phase                        true
% 7.78/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel_side                     none
% 7.78/1.49  --inst_solver_per_active                1400
% 7.78/1.49  --inst_solver_calls_frac                1.
% 7.78/1.49  --inst_passive_queue_type               priority_queues
% 7.78/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.49  --inst_passive_queues_freq              [25;2]
% 7.78/1.49  --inst_dismatching                      true
% 7.78/1.49  --inst_eager_unprocessed_to_passive     true
% 7.78/1.49  --inst_prop_sim_given                   true
% 7.78/1.49  --inst_prop_sim_new                     false
% 7.78/1.49  --inst_subs_new                         false
% 7.78/1.49  --inst_eq_res_simp                      false
% 7.78/1.49  --inst_subs_given                       false
% 7.78/1.49  --inst_orphan_elimination               true
% 7.78/1.49  --inst_learning_loop_flag               true
% 7.78/1.49  --inst_learning_start                   3000
% 7.78/1.49  --inst_learning_factor                  2
% 7.78/1.49  --inst_start_prop_sim_after_learn       3
% 7.78/1.49  --inst_sel_renew                        solver
% 7.78/1.49  --inst_lit_activity_flag                true
% 7.78/1.49  --inst_restr_to_given                   false
% 7.78/1.49  --inst_activity_threshold               500
% 7.78/1.49  --inst_out_proof                        true
% 7.78/1.49  
% 7.78/1.49  ------ Resolution Options
% 7.78/1.49  
% 7.78/1.49  --resolution_flag                       false
% 7.78/1.49  --res_lit_sel                           adaptive
% 7.78/1.49  --res_lit_sel_side                      none
% 7.78/1.49  --res_ordering                          kbo
% 7.78/1.49  --res_to_prop_solver                    active
% 7.78/1.49  --res_prop_simpl_new                    false
% 7.78/1.49  --res_prop_simpl_given                  true
% 7.78/1.49  --res_passive_queue_type                priority_queues
% 7.78/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.49  --res_passive_queues_freq               [15;5]
% 7.78/1.49  --res_forward_subs                      full
% 7.78/1.49  --res_backward_subs                     full
% 7.78/1.49  --res_forward_subs_resolution           true
% 7.78/1.49  --res_backward_subs_resolution          true
% 7.78/1.49  --res_orphan_elimination                true
% 7.78/1.49  --res_time_limit                        2.
% 7.78/1.49  --res_out_proof                         true
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Options
% 7.78/1.49  
% 7.78/1.49  --superposition_flag                    true
% 7.78/1.49  --sup_passive_queue_type                priority_queues
% 7.78/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.49  --demod_completeness_check              fast
% 7.78/1.49  --demod_use_ground                      true
% 7.78/1.49  --sup_to_prop_solver                    passive
% 7.78/1.49  --sup_prop_simpl_new                    true
% 7.78/1.49  --sup_prop_simpl_given                  true
% 7.78/1.49  --sup_fun_splitting                     true
% 7.78/1.49  --sup_smt_interval                      50000
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Simplification Setup
% 7.78/1.49  
% 7.78/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_immed_triv                        [TrivRules]
% 7.78/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_bw_main                     []
% 7.78/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_input_bw                          []
% 7.78/1.49  
% 7.78/1.49  ------ Combination Options
% 7.78/1.49  
% 7.78/1.49  --comb_res_mult                         3
% 7.78/1.49  --comb_sup_mult                         2
% 7.78/1.49  --comb_inst_mult                        10
% 7.78/1.49  
% 7.78/1.49  ------ Debug Options
% 7.78/1.49  
% 7.78/1.49  --dbg_backtrace                         false
% 7.78/1.49  --dbg_dump_prop_clauses                 false
% 7.78/1.49  --dbg_dump_prop_clauses_file            -
% 7.78/1.49  --dbg_out_stat                          false
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS status Theorem for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49   Resolution empty clause
% 7.78/1.49  
% 7.78/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  fof(f4,axiom,(
% 7.78/1.49    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f16,plain,(
% 7.78/1.49    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.78/1.49    inference(ennf_transformation,[],[f4])).
% 7.78/1.49  
% 7.78/1.49  fof(f31,plain,(
% 7.78/1.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f32,plain,(
% 7.78/1.49    ! [X0,X1] : ((sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).
% 7.78/1.49  
% 7.78/1.49  fof(f43,plain,(
% 7.78/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.78/1.49    inference(cnf_transformation,[],[f32])).
% 7.78/1.49  
% 7.78/1.49  fof(f1,axiom,(
% 7.78/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f40,plain,(
% 7.78/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f1])).
% 7.78/1.49  
% 7.78/1.49  fof(f2,axiom,(
% 7.78/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f41,plain,(
% 7.78/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f2])).
% 7.78/1.49  
% 7.78/1.49  fof(f3,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f42,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f3])).
% 7.78/1.49  
% 7.78/1.49  fof(f69,plain,(
% 7.78/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.78/1.49    inference(definition_unfolding,[],[f41,f42])).
% 7.78/1.49  
% 7.78/1.49  fof(f70,plain,(
% 7.78/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.78/1.49    inference(definition_unfolding,[],[f40,f69])).
% 7.78/1.49  
% 7.78/1.49  fof(f72,plain,(
% 7.78/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 7.78/1.49    inference(definition_unfolding,[],[f43,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f14,conjecture,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f15,negated_conjecture,(
% 7.78/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 7.78/1.49    inference(negated_conjecture,[],[f14])).
% 7.78/1.49  
% 7.78/1.49  fof(f29,plain,(
% 7.78/1.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f15])).
% 7.78/1.49  
% 7.78/1.49  fof(f30,plain,(
% 7.78/1.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f29])).
% 7.78/1.49  
% 7.78/1.49  fof(f38,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK4) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK4,X0,k1_tarski(X1)) & v1_funct_1(sK4))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f37,plain,(
% 7.78/1.49    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(X3,sK1,k1_tarski(sK2)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f39,plain,(
% 7.78/1.49    (k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_1(sK3)),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38,f37])).
% 7.78/1.49  
% 7.78/1.49  fof(f64,plain,(
% 7.78/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f83,plain,(
% 7.78/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 7.78/1.49    inference(definition_unfolding,[],[f64,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f13,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f27,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f13])).
% 7.78/1.49  
% 7.78/1.49  fof(f28,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f27])).
% 7.78/1.49  
% 7.78/1.49  fof(f62,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f28])).
% 7.78/1.49  
% 7.78/1.49  fof(f63,plain,(
% 7.78/1.49    v1_funct_1(sK3)),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f9,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f19,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f9])).
% 7.78/1.49  
% 7.78/1.49  fof(f20,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f19])).
% 7.78/1.49  
% 7.78/1.49  fof(f54,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f20])).
% 7.78/1.49  
% 7.78/1.49  fof(f60,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f28])).
% 7.78/1.49  
% 7.78/1.49  fof(f61,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f28])).
% 7.78/1.49  
% 7.78/1.49  fof(f10,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f21,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f10])).
% 7.78/1.49  
% 7.78/1.49  fof(f22,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f21])).
% 7.78/1.49  
% 7.78/1.49  fof(f56,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f22])).
% 7.78/1.49  
% 7.78/1.49  fof(f79,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(definition_unfolding,[],[f56,f70,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f67,plain,(
% 7.78/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f81,plain,(
% 7.78/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 7.78/1.49    inference(definition_unfolding,[],[f67,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f11,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f23,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f11])).
% 7.78/1.49  
% 7.78/1.49  fof(f24,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f23])).
% 7.78/1.49  
% 7.78/1.49  fof(f57,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f24])).
% 7.78/1.49  
% 7.78/1.49  fof(f65,plain,(
% 7.78/1.49    v1_funct_1(sK4)),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f66,plain,(
% 7.78/1.49    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f82,plain,(
% 7.78/1.49    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 7.78/1.49    inference(definition_unfolding,[],[f66,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f68,plain,(
% 7.78/1.49    k1_tarski(sK4) != k5_partfun1(sK1,k1_tarski(sK2),sK3)),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f80,plain,(
% 7.78/1.49    k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 7.78/1.49    inference(definition_unfolding,[],[f68,f70,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f44,plain,(
% 7.78/1.49    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.78/1.49    inference(cnf_transformation,[],[f32])).
% 7.78/1.49  
% 7.78/1.49  fof(f71,plain,(
% 7.78/1.49    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 7.78/1.49    inference(definition_unfolding,[],[f44,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f12,axiom,(
% 7.78/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f25,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.78/1.49    inference(ennf_transformation,[],[f12])).
% 7.78/1.49  
% 7.78/1.49  fof(f26,plain,(
% 7.78/1.49    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.78/1.49    inference(flattening,[],[f25])).
% 7.78/1.49  
% 7.78/1.49  fof(f58,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f26])).
% 7.78/1.49  
% 7.78/1.49  fof(f5,axiom,(
% 7.78/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f33,plain,(
% 7.78/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.78/1.49    inference(nnf_transformation,[],[f5])).
% 7.78/1.49  
% 7.78/1.49  fof(f34,plain,(
% 7.78/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.78/1.49    inference(flattening,[],[f33])).
% 7.78/1.49  
% 7.78/1.49  fof(f46,plain,(
% 7.78/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.78/1.49    inference(cnf_transformation,[],[f34])).
% 7.78/1.49  
% 7.78/1.49  fof(f85,plain,(
% 7.78/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.78/1.49    inference(equality_resolution,[],[f46])).
% 7.78/1.49  
% 7.78/1.49  fof(f6,axiom,(
% 7.78/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f35,plain,(
% 7.78/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.78/1.49    inference(nnf_transformation,[],[f6])).
% 7.78/1.49  
% 7.78/1.49  fof(f36,plain,(
% 7.78/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.78/1.49    inference(flattening,[],[f35])).
% 7.78/1.49  
% 7.78/1.49  fof(f50,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f36])).
% 7.78/1.49  
% 7.78/1.49  fof(f73,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 7.78/1.49    inference(definition_unfolding,[],[f50,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f86,plain,(
% 7.78/1.49    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 7.78/1.49    inference(equality_resolution,[],[f73])).
% 7.78/1.49  
% 7.78/1.49  fof(f49,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 7.78/1.49    inference(cnf_transformation,[],[f36])).
% 7.78/1.49  
% 7.78/1.49  fof(f74,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) )),
% 7.78/1.49    inference(definition_unfolding,[],[f49,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f47,plain,(
% 7.78/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.78/1.49    inference(cnf_transformation,[],[f34])).
% 7.78/1.49  
% 7.78/1.49  fof(f84,plain,(
% 7.78/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.78/1.49    inference(equality_resolution,[],[f47])).
% 7.78/1.49  
% 7.78/1.49  fof(f7,axiom,(
% 7.78/1.49    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f17,plain,(
% 7.78/1.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) | X0 = X1)),
% 7.78/1.49    inference(ennf_transformation,[],[f7])).
% 7.78/1.49  
% 7.78/1.49  fof(f51,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) | X0 = X1) )),
% 7.78/1.49    inference(cnf_transformation,[],[f17])).
% 7.78/1.49  
% 7.78/1.49  fof(f77,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X3)) | X0 = X1) )),
% 7.78/1.49    inference(definition_unfolding,[],[f51,f70,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f8,axiom,(
% 7.78/1.49    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f18,plain,(
% 7.78/1.49    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 7.78/1.49    inference(ennf_transformation,[],[f8])).
% 7.78/1.49  
% 7.78/1.49  fof(f53,plain,(
% 7.78/1.49    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 7.78/1.49    inference(cnf_transformation,[],[f18])).
% 7.78/1.49  
% 7.78/1.49  fof(f78,plain,(
% 7.78/1.49    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 7.78/1.49    inference(definition_unfolding,[],[f53,f70,f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f87,plain,(
% 7.78/1.49    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 7.78/1.49    inference(equality_resolution,[],[f78])).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1,plain,
% 7.78/1.49      ( r2_hidden(sK0(X0,X1),X0)
% 7.78/1.49      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.78/1.49      | k1_xboole_0 = X0 ),
% 7.78/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1034,plain,
% 7.78/1.49      ( k2_enumset1(X0,X0,X0,X0) = X1
% 7.78/1.49      | k1_xboole_0 = X1
% 7.78/1.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_24,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 7.78/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1015,plain,
% 7.78/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_17,plain,
% 7.78/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.78/1.49      | ~ v1_funct_1(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1021,plain,
% 7.78/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.78/1.49      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2405,plain,
% 7.78/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1015,c_1021]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_25,negated_conjecture,
% 7.78/1.49      ( v1_funct_1(sK3) ),
% 7.78/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_26,plain,
% 7.78/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2550,plain,
% 7.78/1.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2405,c_26,c_27,c_2131]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2551,plain,
% 7.78/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_2550]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2556,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | m1_subset_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1034,c_2551]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_12,plain,
% 7.78/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | v1_partfun1(X0,X1)
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | k1_xboole_0 = X2 ),
% 7.78/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1026,plain,
% 7.78/1.49      ( k1_xboole_0 = X0
% 7.78/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.78/1.49      | v1_partfun1(X1,X2) = iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3875,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
% 7.78/1.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2556,c_1026]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_19,plain,
% 7.78/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | v1_funct_1(X3) ),
% 7.78/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1019,plain,
% 7.78/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.49      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(X3) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1402,plain,
% 7.78/1.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) = iProver_top
% 7.78/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1015,c_1019]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1596,plain,
% 7.78/1.49      ( v1_funct_1(X0) = iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1402,c_26]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1597,plain,
% 7.78/1.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) = iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_1596]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1910,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1034,c_1597]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_18,plain,
% 7.78/1.49      ( v1_funct_2(X0,X1,X2)
% 7.78/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 7.78/1.49      | ~ v1_funct_1(X3) ),
% 7.78/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1020,plain,
% 7.78/1.49      ( v1_funct_2(X0,X1,X2) = iProver_top
% 7.78/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
% 7.78/1.49      | v1_funct_1(X3) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1895,plain,
% 7.78/1.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1015,c_1020]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2139,plain,
% 7.78/1.49      ( r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 7.78/1.49      | v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1895,c_26]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2140,plain,
% 7.78/1.49      ( v1_funct_2(X0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_2139]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2145,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | v1_funct_2(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1034,c_2140]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6694,plain,
% 7.78/1.49      ( v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_3875,c_1910,c_2145]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6695,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) = iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_6694]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_13,plain,
% 7.78/1.49      ( r1_partfun1(X0,X1)
% 7.78/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 7.78/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | ~ v1_funct_1(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1025,plain,
% 7.78/1.49      ( r1_partfun1(X0,X1) = iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3890,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top
% 7.78/1.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2556,c_1025]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6005,plain,
% 7.78/1.49      ( v1_funct_1(X1) != iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3890,c_1910]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6006,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | r1_partfun1(X1,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) = iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_6005]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_21,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 7.78/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1018,plain,
% 7.78/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_14,plain,
% 7.78/1.49      ( ~ r1_partfun1(X0,X1)
% 7.78/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.78/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.78/1.49      | ~ v1_partfun1(X1,X2)
% 7.78/1.49      | ~ v1_partfun1(X0,X2)
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | ~ v1_funct_1(X1)
% 7.78/1.49      | X0 = X1 ),
% 7.78/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1024,plain,
% 7.78/1.49      ( X0 = X1
% 7.78/1.49      | r1_partfun1(X0,X1) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.78/1.49      | v1_partfun1(X1,X2) != iProver_top
% 7.78/1.49      | v1_partfun1(X0,X2) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3660,plain,
% 7.78/1.49      ( sK4 = X0
% 7.78/1.49      | r1_partfun1(sK4,X0) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_partfun1(X0,sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1018,c_1024]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_23,negated_conjecture,
% 7.78/1.49      ( v1_funct_1(sK4) ),
% 7.78/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_28,plain,
% 7.78/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4547,plain,
% 7.78/1.49      ( v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(X0,sK1) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | r1_partfun1(sK4,X0) != iProver_top
% 7.78/1.49      | sK4 = X0 ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3660,c_28]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4548,plain,
% 7.78/1.49      ( sK4 = X0
% 7.78/1.49      | r1_partfun1(sK4,X0) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_partfun1(X0,sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_4547]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4556,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_funct_1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2556,c_4548]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_5893,plain,
% 7.78/1.49      ( v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0) ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4556,c_1910]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_5894,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | r1_partfun1(sK4,sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0)) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_5893]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6011,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_6006,c_5894]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_30,plain,
% 7.78/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6601,plain,
% 7.78/1.49      ( v1_partfun1(sK4,sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_6011,c_28,c_30]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6602,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | v1_partfun1(sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0),sK1) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_6601]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6701,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | v1_partfun1(sK4,sK1) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_6695,c_6602]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3872,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.78/1.49      | v1_partfun1(sK4,sK1) = iProver_top
% 7.78/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1018,c_1026]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22,negated_conjecture,
% 7.78/1.49      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_29,plain,
% 7.78/1.49      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4933,plain,
% 7.78/1.49      ( v1_partfun1(sK4,sK1) = iProver_top
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_3872,c_28,c_29]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4934,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | v1_partfun1(sK4,sK1) = iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_4933]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16336,plain,
% 7.78/1.49      ( sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6701,c_4934]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16337,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_16336]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_20,negated_conjecture,
% 7.78/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 7.78/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16404,plain,
% 7.78/1.49      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK0(k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3),X0) = sK4 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16337,c_20]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1083,plain,
% 7.78/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 7.78/1.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != X0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_631]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1121,plain,
% 7.78/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.78/1.49      | k2_enumset1(sK4,sK4,sK4,sK4) = k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_1083]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_630,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1145,plain,
% 7.78/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_630]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_0,plain,
% 7.78/1.49      ( k2_enumset1(X0,X0,X0,X0) = X1 | sK0(X1,X0) != X0 | k1_xboole_0 = X1 ),
% 7.78/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16346,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | sK4 != X0 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16337,c_0]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16576,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 7.78/1.49      inference(equality_resolution,[status(thm)],[c_16346]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16776,plain,
% 7.78/1.49      ( k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_16404,c_20,c_1121,c_1145,c_16576]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16777,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = k1_xboole_0 ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_16776]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16,plain,
% 7.78/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.49      | ~ r1_partfun1(X3,X0)
% 7.78/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.49      | r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 7.78/1.49      | ~ v1_funct_1(X3)
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | k1_xboole_0 = X2 ),
% 7.78/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1022,plain,
% 7.78/1.49      ( k1_xboole_0 = X0
% 7.78/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.78/1.49      | r1_partfun1(X3,X1) != iProver_top
% 7.78/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.78/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.78/1.49      | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
% 7.78/1.49      | v1_funct_1(X1) != iProver_top
% 7.78/1.49      | v1_funct_1(X3) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2923,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.78/1.49      | r1_partfun1(X0,sK4) != iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1018,c_1022]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2360,plain,
% 7.78/1.49      ( r1_partfun1(X0,sK4)
% 7.78/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))
% 7.78/1.49      | ~ v1_funct_1(X0)
% 7.78/1.49      | ~ v1_funct_1(sK4) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2361,plain,
% 7.78/1.49      ( r1_partfun1(X0,sK4) = iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top
% 7.78/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3236,plain,
% 7.78/1.49      ( v1_funct_1(X0) != iProver_top
% 7.78/1.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2923,c_28,c_29,c_30,c_2361]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3237,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 7.78/1.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),X0)) = iProver_top
% 7.78/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_3236]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3243,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 7.78/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1015,c_3237]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3410,plain,
% 7.78/1.49      ( r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 7.78/1.49      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3243,c_26]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3411,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | r2_hidden(sK4,k5_partfun1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_3410]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16794,plain,
% 7.78/1.49      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 7.78/1.49      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16777,c_3411]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3,plain,
% 7.78/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.78/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_5,plain,
% 7.78/1.49      ( ~ r2_hidden(X0,X1)
% 7.78/1.49      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) ),
% 7.78/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1033,plain,
% 7.78/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.78/1.49      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1859,plain,
% 7.78/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.78/1.49      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_3,c_1033]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6,plain,
% 7.78/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
% 7.78/1.49      | X3 = X1 ),
% 7.78/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1032,plain,
% 7.78/1.49      ( X0 = X1
% 7.78/1.49      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1636,plain,
% 7.78/1.49      ( X0 = X1 | r2_hidden(k4_tarski(X2,X1),k1_xboole_0) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_3,c_1032]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1867,plain,
% 7.78/1.49      ( X0 = X1 | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1859,c_1636]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16947,plain,
% 7.78/1.49      ( X0 = X1 | k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16794,c_1867]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_17526,plain,
% 7.78/1.49      ( X0 = X1
% 7.78/1.49      | k2_enumset1(sK4,sK4,sK4,sK4) != k5_partfun1(sK1,k1_xboole_0,sK3) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16947,c_20]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2,plain,
% 7.78/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.78/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_9,plain,
% 7.78/1.49      ( r1_xboole_0(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 7.78/1.49      | X2 = X0 ),
% 7.78/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1029,plain,
% 7.78/1.49      ( X0 = X1
% 7.78/1.49      | r1_xboole_0(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1972,plain,
% 7.78/1.49      ( X0 = X1
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2,c_1029]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1977,plain,
% 7.78/1.49      ( X0 = X1 | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2,c_1972]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_10,plain,
% 7.78/1.49      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1028,plain,
% 7.78/1.49      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_17434,plain,
% 7.78/1.49      ( X0 = X1 | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_16947,c_1028]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_19525,plain,
% 7.78/1.49      ( X0 = X1 ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_17526,c_1977,c_17434]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_19744,plain,
% 7.78/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_19525,c_20]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_19897,plain,
% 7.78/1.49      ( $false ),
% 7.78/1.49      inference(equality_resolution,[status(thm)],[c_19744]) ).
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  ------                               Statistics
% 7.78/1.49  
% 7.78/1.49  ------ General
% 7.78/1.49  
% 7.78/1.49  abstr_ref_over_cycles:                  0
% 7.78/1.49  abstr_ref_under_cycles:                 0
% 7.78/1.49  gc_basic_clause_elim:                   0
% 7.78/1.49  forced_gc_time:                         0
% 7.78/1.49  parsing_time:                           0.009
% 7.78/1.49  unif_index_cands_time:                  0.
% 7.78/1.49  unif_index_add_time:                    0.
% 7.78/1.49  orderings_time:                         0.
% 7.78/1.49  out_proof_time:                         0.014
% 7.78/1.49  total_time:                             0.668
% 7.78/1.49  num_of_symbols:                         49
% 7.78/1.49  num_of_terms:                           15280
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing
% 7.78/1.49  
% 7.78/1.49  num_of_splits:                          0
% 7.78/1.49  num_of_split_atoms:                     0
% 7.78/1.49  num_of_reused_defs:                     0
% 7.78/1.49  num_eq_ax_congr_red:                    14
% 7.78/1.49  num_of_sem_filtered_clauses:            1
% 7.78/1.49  num_of_subtypes:                        0
% 7.78/1.49  monotx_restored_types:                  0
% 7.78/1.49  sat_num_of_epr_types:                   0
% 7.78/1.49  sat_num_of_non_cyclic_types:            0
% 7.78/1.49  sat_guarded_non_collapsed_types:        0
% 7.78/1.49  num_pure_diseq_elim:                    0
% 7.78/1.49  simp_replaced_by:                       0
% 7.78/1.49  res_preprocessed:                       103
% 7.78/1.49  prep_upred:                             0
% 7.78/1.49  prep_unflattend:                        20
% 7.78/1.49  smt_new_axioms:                         0
% 7.78/1.49  pred_elim_cands:                        7
% 7.78/1.49  pred_elim:                              0
% 7.78/1.49  pred_elim_cl:                           0
% 7.78/1.49  pred_elim_cycles:                       3
% 7.78/1.49  merged_defs:                            0
% 7.78/1.49  merged_defs_ncl:                        0
% 7.78/1.49  bin_hyper_res:                          0
% 7.78/1.49  prep_cycles:                            3
% 7.78/1.49  pred_elim_time:                         0.009
% 7.78/1.49  splitting_time:                         0.
% 7.78/1.49  sem_filter_time:                        0.
% 7.78/1.49  monotx_time:                            0.
% 7.78/1.49  subtype_inf_time:                       0.
% 7.78/1.49  
% 7.78/1.49  ------ Problem properties
% 7.78/1.49  
% 7.78/1.49  clauses:                                26
% 7.78/1.49  conjectures:                            6
% 7.78/1.49  epr:                                    2
% 7.78/1.49  horn:                                   19
% 7.78/1.49  ground:                                 6
% 7.78/1.49  unary:                                  9
% 7.78/1.49  binary:                                 5
% 7.78/1.49  lits:                                   77
% 7.78/1.49  lits_eq:                                17
% 7.78/1.49  fd_pure:                                0
% 7.78/1.49  fd_pseudo:                              0
% 7.78/1.49  fd_cond:                                3
% 7.78/1.49  fd_pseudo_cond:                         6
% 7.78/1.49  ac_symbols:                             0
% 7.78/1.49  
% 7.78/1.49  ------ Propositional Solver
% 7.78/1.49  
% 7.78/1.49  prop_solver_calls:                      30
% 7.78/1.49  prop_fast_solver_calls:                 2163
% 7.78/1.49  smt_solver_calls:                       0
% 7.78/1.49  smt_fast_solver_calls:                  0
% 7.78/1.49  prop_num_of_clauses:                    6493
% 7.78/1.49  prop_preprocess_simplified:             9626
% 7.78/1.49  prop_fo_subsumed:                       124
% 7.78/1.49  prop_solver_time:                       0.
% 7.78/1.49  smt_solver_time:                        0.
% 7.78/1.49  smt_fast_solver_time:                   0.
% 7.78/1.49  prop_fast_solver_time:                  0.
% 7.78/1.49  prop_unsat_core_time:                   0.
% 7.78/1.49  
% 7.78/1.49  ------ QBF
% 7.78/1.49  
% 7.78/1.49  qbf_q_res:                              0
% 7.78/1.49  qbf_num_tautologies:                    0
% 7.78/1.49  qbf_prep_cycles:                        0
% 7.78/1.49  
% 7.78/1.49  ------ BMC1
% 7.78/1.49  
% 7.78/1.49  bmc1_current_bound:                     -1
% 7.78/1.49  bmc1_last_solved_bound:                 -1
% 7.78/1.49  bmc1_unsat_core_size:                   -1
% 7.78/1.49  bmc1_unsat_core_parents_size:           -1
% 7.78/1.49  bmc1_merge_next_fun:                    0
% 7.78/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation
% 7.78/1.49  
% 7.78/1.49  inst_num_of_clauses:                    1437
% 7.78/1.49  inst_num_in_passive:                    688
% 7.78/1.49  inst_num_in_active:                     740
% 7.78/1.49  inst_num_in_unprocessed:                9
% 7.78/1.49  inst_num_of_loops:                      1060
% 7.78/1.49  inst_num_of_learning_restarts:          0
% 7.78/1.49  inst_num_moves_active_passive:          313
% 7.78/1.49  inst_lit_activity:                      0
% 7.78/1.49  inst_lit_activity_moves:                0
% 7.78/1.49  inst_num_tautologies:                   0
% 7.78/1.49  inst_num_prop_implied:                  0
% 7.78/1.49  inst_num_existing_simplified:           0
% 7.78/1.49  inst_num_eq_res_simplified:             0
% 7.78/1.49  inst_num_child_elim:                    0
% 7.78/1.49  inst_num_of_dismatching_blockings:      1369
% 7.78/1.49  inst_num_of_non_proper_insts:           2692
% 7.78/1.49  inst_num_of_duplicates:                 0
% 7.78/1.49  inst_inst_num_from_inst_to_res:         0
% 7.78/1.49  inst_dismatching_checking_time:         0.
% 7.78/1.49  
% 7.78/1.49  ------ Resolution
% 7.78/1.49  
% 7.78/1.49  res_num_of_clauses:                     0
% 7.78/1.49  res_num_in_passive:                     0
% 7.78/1.49  res_num_in_active:                      0
% 7.78/1.49  res_num_of_loops:                       106
% 7.78/1.49  res_forward_subset_subsumed:            376
% 7.78/1.49  res_backward_subset_subsumed:           4
% 7.78/1.49  res_forward_subsumed:                   0
% 7.78/1.49  res_backward_subsumed:                  0
% 7.78/1.49  res_forward_subsumption_resolution:     6
% 7.78/1.49  res_backward_subsumption_resolution:    0
% 7.78/1.49  res_clause_to_clause_subsumption:       3410
% 7.78/1.49  res_orphan_elimination:                 0
% 7.78/1.49  res_tautology_del:                      195
% 7.78/1.49  res_num_eq_res_simplified:              0
% 7.78/1.49  res_num_sel_changes:                    0
% 7.78/1.49  res_moves_from_active_to_pass:          0
% 7.78/1.49  
% 7.78/1.49  ------ Superposition
% 7.78/1.49  
% 7.78/1.49  sup_time_total:                         0.
% 7.78/1.49  sup_time_generating:                    0.
% 7.78/1.49  sup_time_sim_full:                      0.
% 7.78/1.49  sup_time_sim_immed:                     0.
% 7.78/1.49  
% 7.78/1.49  sup_num_of_clauses:                     372
% 7.78/1.49  sup_num_in_active:                      16
% 7.78/1.49  sup_num_in_passive:                     356
% 7.78/1.49  sup_num_of_loops:                       211
% 7.78/1.49  sup_fw_superposition:                   321
% 7.78/1.49  sup_bw_superposition:                   2835
% 7.78/1.49  sup_immediate_simplified:               928
% 7.78/1.49  sup_given_eliminated:                   0
% 7.78/1.49  comparisons_done:                       0
% 7.78/1.49  comparisons_avoided:                    368
% 7.78/1.49  
% 7.78/1.49  ------ Simplifications
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  sim_fw_subset_subsumed:                 216
% 7.78/1.49  sim_bw_subset_subsumed:                 149
% 7.78/1.49  sim_fw_subsumed:                        637
% 7.78/1.49  sim_bw_subsumed:                        153
% 7.78/1.49  sim_fw_subsumption_res:                 0
% 7.78/1.49  sim_bw_subsumption_res:                 0
% 7.78/1.49  sim_tautology_del:                      30
% 7.78/1.49  sim_eq_tautology_del:                   9
% 7.78/1.49  sim_eq_res_simp:                        0
% 7.78/1.49  sim_fw_demodulated:                     29
% 7.78/1.49  sim_bw_demodulated:                     71
% 7.78/1.49  sim_light_normalised:                   1
% 7.78/1.49  sim_joinable_taut:                      0
% 7.78/1.49  sim_joinable_simp:                      0
% 7.78/1.49  sim_ac_normalised:                      0
% 7.78/1.49  sim_smt_subsumption:                    0
% 7.78/1.49  
%------------------------------------------------------------------------------
