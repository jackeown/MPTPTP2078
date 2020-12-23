%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:33 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 204 expanded)
%              Number of clauses        :   30 (  31 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  246 ( 558 expanded)
%              Number of equality atoms :  118 ( 280 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f58])).

fof(f69,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f27])).

fof(f49,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f58])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f52,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_691,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_996,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1000,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_597,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_849,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_597])).

cnf(c_855,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_849])).

cnf(c_857,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_701,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_funct_1(sK4,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_184,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_185,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_189,plain,
    ( r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_185,c_16])).

cnf(c_190,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK4,X0),X2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_190])).

cnf(c_218,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_218])).

cnf(c_673,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK3,sK1)
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_3,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1000,c_857,c_701,c_673,c_40,c_37,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:39:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/0.98  
% 0.99/0.98  ------  iProver source info
% 0.99/0.98  
% 0.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/0.98  git: non_committed_changes: false
% 0.99/0.98  git: last_make_outside_of_git: false
% 0.99/0.98  
% 0.99/0.98  ------ 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options
% 0.99/0.98  
% 0.99/0.98  --out_options                           all
% 0.99/0.98  --tptp_safe_out                         true
% 0.99/0.98  --problem_path                          ""
% 0.99/0.98  --include_path                          ""
% 0.99/0.98  --clausifier                            res/vclausify_rel
% 0.99/0.98  --clausifier_options                    --mode clausify
% 0.99/0.98  --stdin                                 false
% 0.99/0.98  --stats_out                             all
% 0.99/0.98  
% 0.99/0.98  ------ General Options
% 0.99/0.98  
% 0.99/0.98  --fof                                   false
% 0.99/0.98  --time_out_real                         305.
% 0.99/0.98  --time_out_virtual                      -1.
% 0.99/0.98  --symbol_type_check                     false
% 0.99/0.98  --clausify_out                          false
% 0.99/0.98  --sig_cnt_out                           false
% 0.99/0.98  --trig_cnt_out                          false
% 0.99/0.98  --trig_cnt_out_tolerance                1.
% 0.99/0.98  --trig_cnt_out_sk_spl                   false
% 0.99/0.98  --abstr_cl_out                          false
% 0.99/0.98  
% 0.99/0.98  ------ Global Options
% 0.99/0.98  
% 0.99/0.98  --schedule                              default
% 0.99/0.98  --add_important_lit                     false
% 0.99/0.98  --prop_solver_per_cl                    1000
% 0.99/0.98  --min_unsat_core                        false
% 0.99/0.98  --soft_assumptions                      false
% 0.99/0.98  --soft_lemma_size                       3
% 0.99/0.98  --prop_impl_unit_size                   0
% 0.99/0.98  --prop_impl_unit                        []
% 0.99/0.98  --share_sel_clauses                     true
% 0.99/0.98  --reset_solvers                         false
% 0.99/0.98  --bc_imp_inh                            [conj_cone]
% 0.99/0.98  --conj_cone_tolerance                   3.
% 0.99/0.98  --extra_neg_conj                        none
% 0.99/0.98  --large_theory_mode                     true
% 0.99/0.98  --prolific_symb_bound                   200
% 0.99/0.98  --lt_threshold                          2000
% 0.99/0.98  --clause_weak_htbl                      true
% 0.99/0.98  --gc_record_bc_elim                     false
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing Options
% 0.99/0.98  
% 0.99/0.98  --preprocessing_flag                    true
% 0.99/0.98  --time_out_prep_mult                    0.1
% 0.99/0.98  --splitting_mode                        input
% 0.99/0.98  --splitting_grd                         true
% 0.99/0.98  --splitting_cvd                         false
% 0.99/0.98  --splitting_cvd_svl                     false
% 0.99/0.98  --splitting_nvd                         32
% 0.99/0.98  --sub_typing                            true
% 0.99/0.98  --prep_gs_sim                           true
% 0.99/0.98  --prep_unflatten                        true
% 0.99/0.98  --prep_res_sim                          true
% 0.99/0.98  --prep_upred                            true
% 0.99/0.98  --prep_sem_filter                       exhaustive
% 0.99/0.98  --prep_sem_filter_out                   false
% 0.99/0.98  --pred_elim                             true
% 0.99/0.98  --res_sim_input                         true
% 0.99/0.98  --eq_ax_congr_red                       true
% 0.99/0.98  --pure_diseq_elim                       true
% 0.99/0.98  --brand_transform                       false
% 0.99/0.98  --non_eq_to_eq                          false
% 0.99/0.98  --prep_def_merge                        true
% 0.99/0.98  --prep_def_merge_prop_impl              false
% 0.99/0.98  --prep_def_merge_mbd                    true
% 0.99/0.98  --prep_def_merge_tr_red                 false
% 0.99/0.98  --prep_def_merge_tr_cl                  false
% 0.99/0.98  --smt_preprocessing                     true
% 0.99/0.98  --smt_ac_axioms                         fast
% 0.99/0.98  --preprocessed_out                      false
% 0.99/0.98  --preprocessed_stats                    false
% 0.99/0.98  
% 0.99/0.98  ------ Abstraction refinement Options
% 0.99/0.98  
% 0.99/0.98  --abstr_ref                             []
% 0.99/0.98  --abstr_ref_prep                        false
% 0.99/0.98  --abstr_ref_until_sat                   false
% 0.99/0.98  --abstr_ref_sig_restrict                funpre
% 0.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.98  --abstr_ref_under                       []
% 0.99/0.98  
% 0.99/0.98  ------ SAT Options
% 0.99/0.98  
% 0.99/0.98  --sat_mode                              false
% 0.99/0.98  --sat_fm_restart_options                ""
% 0.99/0.98  --sat_gr_def                            false
% 0.99/0.98  --sat_epr_types                         true
% 0.99/0.98  --sat_non_cyclic_types                  false
% 0.99/0.98  --sat_finite_models                     false
% 0.99/0.98  --sat_fm_lemmas                         false
% 0.99/0.98  --sat_fm_prep                           false
% 0.99/0.98  --sat_fm_uc_incr                        true
% 0.99/0.98  --sat_out_model                         small
% 0.99/0.98  --sat_out_clauses                       false
% 0.99/0.98  
% 0.99/0.98  ------ QBF Options
% 0.99/0.98  
% 0.99/0.98  --qbf_mode                              false
% 0.99/0.98  --qbf_elim_univ                         false
% 0.99/0.98  --qbf_dom_inst                          none
% 0.99/0.98  --qbf_dom_pre_inst                      false
% 0.99/0.98  --qbf_sk_in                             false
% 0.99/0.98  --qbf_pred_elim                         true
% 0.99/0.98  --qbf_split                             512
% 0.99/0.98  
% 0.99/0.98  ------ BMC1 Options
% 0.99/0.98  
% 0.99/0.98  --bmc1_incremental                      false
% 0.99/0.98  --bmc1_axioms                           reachable_all
% 0.99/0.98  --bmc1_min_bound                        0
% 0.99/0.98  --bmc1_max_bound                        -1
% 0.99/0.98  --bmc1_max_bound_default                -1
% 0.99/0.98  --bmc1_symbol_reachability              true
% 0.99/0.98  --bmc1_property_lemmas                  false
% 0.99/0.98  --bmc1_k_induction                      false
% 0.99/0.98  --bmc1_non_equiv_states                 false
% 0.99/0.98  --bmc1_deadlock                         false
% 0.99/0.98  --bmc1_ucm                              false
% 0.99/0.98  --bmc1_add_unsat_core                   none
% 0.99/0.98  --bmc1_unsat_core_children              false
% 0.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.98  --bmc1_out_stat                         full
% 0.99/0.98  --bmc1_ground_init                      false
% 0.99/0.98  --bmc1_pre_inst_next_state              false
% 0.99/0.98  --bmc1_pre_inst_state                   false
% 0.99/0.98  --bmc1_pre_inst_reach_state             false
% 0.99/0.98  --bmc1_out_unsat_core                   false
% 0.99/0.98  --bmc1_aig_witness_out                  false
% 0.99/0.98  --bmc1_verbose                          false
% 0.99/0.98  --bmc1_dump_clauses_tptp                false
% 0.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.98  --bmc1_dump_file                        -
% 0.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.98  --bmc1_ucm_extend_mode                  1
% 0.99/0.98  --bmc1_ucm_init_mode                    2
% 0.99/0.98  --bmc1_ucm_cone_mode                    none
% 0.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.98  --bmc1_ucm_relax_model                  4
% 0.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.98  --bmc1_ucm_layered_model                none
% 0.99/0.98  --bmc1_ucm_max_lemma_size               10
% 0.99/0.98  
% 0.99/0.98  ------ AIG Options
% 0.99/0.98  
% 0.99/0.98  --aig_mode                              false
% 0.99/0.98  
% 0.99/0.98  ------ Instantiation Options
% 0.99/0.98  
% 0.99/0.98  --instantiation_flag                    true
% 0.99/0.98  --inst_sos_flag                         false
% 0.99/0.98  --inst_sos_phase                        true
% 0.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel_side                     num_symb
% 0.99/0.98  --inst_solver_per_active                1400
% 0.99/0.98  --inst_solver_calls_frac                1.
% 0.99/0.98  --inst_passive_queue_type               priority_queues
% 0.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.98  --inst_passive_queues_freq              [25;2]
% 0.99/0.98  --inst_dismatching                      true
% 0.99/0.98  --inst_eager_unprocessed_to_passive     true
% 0.99/0.98  --inst_prop_sim_given                   true
% 0.99/0.98  --inst_prop_sim_new                     false
% 0.99/0.98  --inst_subs_new                         false
% 0.99/0.98  --inst_eq_res_simp                      false
% 0.99/0.98  --inst_subs_given                       false
% 0.99/0.98  --inst_orphan_elimination               true
% 0.99/0.98  --inst_learning_loop_flag               true
% 0.99/0.98  --inst_learning_start                   3000
% 0.99/0.98  --inst_learning_factor                  2
% 0.99/0.98  --inst_start_prop_sim_after_learn       3
% 0.99/0.98  --inst_sel_renew                        solver
% 0.99/0.98  --inst_lit_activity_flag                true
% 0.99/0.98  --inst_restr_to_given                   false
% 0.99/0.98  --inst_activity_threshold               500
% 0.99/0.98  --inst_out_proof                        true
% 0.99/0.98  
% 0.99/0.98  ------ Resolution Options
% 0.99/0.98  
% 0.99/0.98  --resolution_flag                       true
% 0.99/0.98  --res_lit_sel                           adaptive
% 0.99/0.98  --res_lit_sel_side                      none
% 0.99/0.98  --res_ordering                          kbo
% 0.99/0.98  --res_to_prop_solver                    active
% 0.99/0.98  --res_prop_simpl_new                    false
% 0.99/0.98  --res_prop_simpl_given                  true
% 0.99/0.98  --res_passive_queue_type                priority_queues
% 0.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.98  --res_passive_queues_freq               [15;5]
% 0.99/0.98  --res_forward_subs                      full
% 0.99/0.98  --res_backward_subs                     full
% 0.99/0.98  --res_forward_subs_resolution           true
% 0.99/0.98  --res_backward_subs_resolution          true
% 0.99/0.98  --res_orphan_elimination                true
% 0.99/0.98  --res_time_limit                        2.
% 0.99/0.98  --res_out_proof                         true
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Options
% 0.99/0.98  
% 0.99/0.98  --superposition_flag                    true
% 0.99/0.98  --sup_passive_queue_type                priority_queues
% 0.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.98  --demod_completeness_check              fast
% 0.99/0.98  --demod_use_ground                      true
% 0.99/0.98  --sup_to_prop_solver                    passive
% 0.99/0.98  --sup_prop_simpl_new                    true
% 0.99/0.98  --sup_prop_simpl_given                  true
% 0.99/0.98  --sup_fun_splitting                     false
% 0.99/0.98  --sup_smt_interval                      50000
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Simplification Setup
% 0.99/0.98  
% 0.99/0.98  --sup_indices_passive                   []
% 0.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_full_bw                           [BwDemod]
% 0.99/0.98  --sup_immed_triv                        [TrivRules]
% 0.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_immed_bw_main                     []
% 0.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  
% 0.99/0.98  ------ Combination Options
% 0.99/0.98  
% 0.99/0.98  --comb_res_mult                         3
% 0.99/0.98  --comb_sup_mult                         2
% 0.99/0.98  --comb_inst_mult                        10
% 0.99/0.98  
% 0.99/0.98  ------ Debug Options
% 0.99/0.98  
% 0.99/0.98  --dbg_backtrace                         false
% 0.99/0.98  --dbg_dump_prop_clauses                 false
% 0.99/0.98  --dbg_dump_prop_clauses_file            -
% 0.99/0.98  --dbg_out_stat                          false
% 0.99/0.98  ------ Parsing...
% 0.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/0.98  ------ Proving...
% 0.99/0.98  ------ Problem Properties 
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  clauses                                 14
% 0.99/0.98  conjectures                             2
% 0.99/0.98  EPR                                     1
% 0.99/0.98  Horn                                    11
% 0.99/0.98  unary                                   7
% 0.99/0.98  binary                                  3
% 0.99/0.98  lits                                    25
% 0.99/0.98  lits eq                                 15
% 0.99/0.98  fd_pure                                 0
% 0.99/0.98  fd_pseudo                               0
% 0.99/0.98  fd_cond                                 1
% 0.99/0.98  fd_pseudo_cond                          2
% 0.99/0.98  AC symbols                              0
% 0.99/0.98  
% 0.99/0.98  ------ Schedule dynamic 5 is on 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  ------ 
% 0.99/0.98  Current options:
% 0.99/0.98  ------ 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options
% 0.99/0.98  
% 0.99/0.98  --out_options                           all
% 0.99/0.98  --tptp_safe_out                         true
% 0.99/0.98  --problem_path                          ""
% 0.99/0.98  --include_path                          ""
% 0.99/0.98  --clausifier                            res/vclausify_rel
% 0.99/0.98  --clausifier_options                    --mode clausify
% 0.99/0.98  --stdin                                 false
% 0.99/0.98  --stats_out                             all
% 0.99/0.98  
% 0.99/0.98  ------ General Options
% 0.99/0.98  
% 0.99/0.98  --fof                                   false
% 0.99/0.98  --time_out_real                         305.
% 0.99/0.98  --time_out_virtual                      -1.
% 0.99/0.98  --symbol_type_check                     false
% 0.99/0.98  --clausify_out                          false
% 0.99/0.98  --sig_cnt_out                           false
% 0.99/0.98  --trig_cnt_out                          false
% 0.99/0.98  --trig_cnt_out_tolerance                1.
% 0.99/0.98  --trig_cnt_out_sk_spl                   false
% 0.99/0.98  --abstr_cl_out                          false
% 0.99/0.98  
% 0.99/0.98  ------ Global Options
% 0.99/0.98  
% 0.99/0.98  --schedule                              default
% 0.99/0.98  --add_important_lit                     false
% 0.99/0.98  --prop_solver_per_cl                    1000
% 0.99/0.98  --min_unsat_core                        false
% 0.99/0.98  --soft_assumptions                      false
% 0.99/0.98  --soft_lemma_size                       3
% 0.99/0.98  --prop_impl_unit_size                   0
% 0.99/0.98  --prop_impl_unit                        []
% 0.99/0.98  --share_sel_clauses                     true
% 0.99/0.98  --reset_solvers                         false
% 0.99/0.98  --bc_imp_inh                            [conj_cone]
% 0.99/0.98  --conj_cone_tolerance                   3.
% 0.99/0.98  --extra_neg_conj                        none
% 0.99/0.98  --large_theory_mode                     true
% 0.99/0.98  --prolific_symb_bound                   200
% 0.99/0.98  --lt_threshold                          2000
% 0.99/0.98  --clause_weak_htbl                      true
% 0.99/0.98  --gc_record_bc_elim                     false
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing Options
% 0.99/0.98  
% 0.99/0.98  --preprocessing_flag                    true
% 0.99/0.98  --time_out_prep_mult                    0.1
% 0.99/0.98  --splitting_mode                        input
% 0.99/0.98  --splitting_grd                         true
% 0.99/0.98  --splitting_cvd                         false
% 0.99/0.98  --splitting_cvd_svl                     false
% 0.99/0.98  --splitting_nvd                         32
% 0.99/0.98  --sub_typing                            true
% 0.99/0.98  --prep_gs_sim                           true
% 0.99/0.98  --prep_unflatten                        true
% 0.99/0.98  --prep_res_sim                          true
% 0.99/0.98  --prep_upred                            true
% 0.99/0.98  --prep_sem_filter                       exhaustive
% 0.99/0.98  --prep_sem_filter_out                   false
% 0.99/0.98  --pred_elim                             true
% 0.99/0.98  --res_sim_input                         true
% 0.99/0.98  --eq_ax_congr_red                       true
% 0.99/0.98  --pure_diseq_elim                       true
% 0.99/0.98  --brand_transform                       false
% 0.99/0.98  --non_eq_to_eq                          false
% 0.99/0.98  --prep_def_merge                        true
% 0.99/0.98  --prep_def_merge_prop_impl              false
% 0.99/0.98  --prep_def_merge_mbd                    true
% 0.99/0.98  --prep_def_merge_tr_red                 false
% 0.99/0.98  --prep_def_merge_tr_cl                  false
% 0.99/0.98  --smt_preprocessing                     true
% 0.99/0.98  --smt_ac_axioms                         fast
% 0.99/0.98  --preprocessed_out                      false
% 0.99/0.98  --preprocessed_stats                    false
% 0.99/0.98  
% 0.99/0.98  ------ Abstraction refinement Options
% 0.99/0.98  
% 0.99/0.98  --abstr_ref                             []
% 0.99/0.98  --abstr_ref_prep                        false
% 0.99/0.98  --abstr_ref_until_sat                   false
% 0.99/0.98  --abstr_ref_sig_restrict                funpre
% 0.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.98  --abstr_ref_under                       []
% 0.99/0.98  
% 0.99/0.98  ------ SAT Options
% 0.99/0.98  
% 0.99/0.98  --sat_mode                              false
% 0.99/0.98  --sat_fm_restart_options                ""
% 0.99/0.98  --sat_gr_def                            false
% 0.99/0.98  --sat_epr_types                         true
% 0.99/0.98  --sat_non_cyclic_types                  false
% 0.99/0.98  --sat_finite_models                     false
% 0.99/0.98  --sat_fm_lemmas                         false
% 0.99/0.98  --sat_fm_prep                           false
% 0.99/0.98  --sat_fm_uc_incr                        true
% 0.99/0.98  --sat_out_model                         small
% 0.99/0.98  --sat_out_clauses                       false
% 0.99/0.98  
% 0.99/0.98  ------ QBF Options
% 0.99/0.98  
% 0.99/0.98  --qbf_mode                              false
% 0.99/0.98  --qbf_elim_univ                         false
% 0.99/0.98  --qbf_dom_inst                          none
% 0.99/0.98  --qbf_dom_pre_inst                      false
% 0.99/0.98  --qbf_sk_in                             false
% 0.99/0.98  --qbf_pred_elim                         true
% 0.99/0.98  --qbf_split                             512
% 0.99/0.98  
% 0.99/0.98  ------ BMC1 Options
% 0.99/0.98  
% 0.99/0.98  --bmc1_incremental                      false
% 0.99/0.98  --bmc1_axioms                           reachable_all
% 0.99/0.98  --bmc1_min_bound                        0
% 0.99/0.98  --bmc1_max_bound                        -1
% 0.99/0.98  --bmc1_max_bound_default                -1
% 0.99/0.98  --bmc1_symbol_reachability              true
% 0.99/0.98  --bmc1_property_lemmas                  false
% 0.99/0.98  --bmc1_k_induction                      false
% 0.99/0.98  --bmc1_non_equiv_states                 false
% 0.99/0.98  --bmc1_deadlock                         false
% 0.99/0.98  --bmc1_ucm                              false
% 0.99/0.98  --bmc1_add_unsat_core                   none
% 0.99/0.98  --bmc1_unsat_core_children              false
% 0.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.98  --bmc1_out_stat                         full
% 0.99/0.98  --bmc1_ground_init                      false
% 0.99/0.98  --bmc1_pre_inst_next_state              false
% 0.99/0.98  --bmc1_pre_inst_state                   false
% 0.99/0.98  --bmc1_pre_inst_reach_state             false
% 0.99/0.98  --bmc1_out_unsat_core                   false
% 0.99/0.98  --bmc1_aig_witness_out                  false
% 0.99/0.98  --bmc1_verbose                          false
% 0.99/0.98  --bmc1_dump_clauses_tptp                false
% 0.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.98  --bmc1_dump_file                        -
% 0.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.98  --bmc1_ucm_extend_mode                  1
% 0.99/0.98  --bmc1_ucm_init_mode                    2
% 0.99/0.98  --bmc1_ucm_cone_mode                    none
% 0.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.98  --bmc1_ucm_relax_model                  4
% 0.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.98  --bmc1_ucm_layered_model                none
% 0.99/0.98  --bmc1_ucm_max_lemma_size               10
% 0.99/0.98  
% 0.99/0.98  ------ AIG Options
% 0.99/0.98  
% 0.99/0.98  --aig_mode                              false
% 0.99/0.98  
% 0.99/0.98  ------ Instantiation Options
% 0.99/0.98  
% 0.99/0.98  --instantiation_flag                    true
% 0.99/0.98  --inst_sos_flag                         false
% 0.99/0.98  --inst_sos_phase                        true
% 0.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel_side                     none
% 0.99/0.98  --inst_solver_per_active                1400
% 0.99/0.98  --inst_solver_calls_frac                1.
% 0.99/0.98  --inst_passive_queue_type               priority_queues
% 0.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.98  --inst_passive_queues_freq              [25;2]
% 0.99/0.98  --inst_dismatching                      true
% 0.99/0.98  --inst_eager_unprocessed_to_passive     true
% 0.99/0.98  --inst_prop_sim_given                   true
% 0.99/0.98  --inst_prop_sim_new                     false
% 0.99/0.98  --inst_subs_new                         false
% 0.99/0.98  --inst_eq_res_simp                      false
% 0.99/0.98  --inst_subs_given                       false
% 0.99/0.98  --inst_orphan_elimination               true
% 0.99/0.98  --inst_learning_loop_flag               true
% 0.99/0.98  --inst_learning_start                   3000
% 0.99/0.98  --inst_learning_factor                  2
% 0.99/0.98  --inst_start_prop_sim_after_learn       3
% 0.99/0.98  --inst_sel_renew                        solver
% 0.99/0.98  --inst_lit_activity_flag                true
% 0.99/0.98  --inst_restr_to_given                   false
% 0.99/0.98  --inst_activity_threshold               500
% 0.99/0.98  --inst_out_proof                        true
% 0.99/0.98  
% 0.99/0.98  ------ Resolution Options
% 0.99/0.98  
% 0.99/0.98  --resolution_flag                       false
% 0.99/0.98  --res_lit_sel                           adaptive
% 0.99/0.98  --res_lit_sel_side                      none
% 0.99/0.98  --res_ordering                          kbo
% 0.99/0.98  --res_to_prop_solver                    active
% 0.99/0.98  --res_prop_simpl_new                    false
% 0.99/0.98  --res_prop_simpl_given                  true
% 0.99/0.98  --res_passive_queue_type                priority_queues
% 0.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.98  --res_passive_queues_freq               [15;5]
% 0.99/0.98  --res_forward_subs                      full
% 0.99/0.98  --res_backward_subs                     full
% 0.99/0.98  --res_forward_subs_resolution           true
% 0.99/0.98  --res_backward_subs_resolution          true
% 0.99/0.98  --res_orphan_elimination                true
% 0.99/0.98  --res_time_limit                        2.
% 0.99/0.98  --res_out_proof                         true
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Options
% 0.99/0.98  
% 0.99/0.98  --superposition_flag                    true
% 0.99/0.98  --sup_passive_queue_type                priority_queues
% 0.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.98  --demod_completeness_check              fast
% 0.99/0.98  --demod_use_ground                      true
% 0.99/0.98  --sup_to_prop_solver                    passive
% 0.99/0.98  --sup_prop_simpl_new                    true
% 0.99/0.98  --sup_prop_simpl_given                  true
% 0.99/0.98  --sup_fun_splitting                     false
% 0.99/0.98  --sup_smt_interval                      50000
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Simplification Setup
% 0.99/0.98  
% 0.99/0.98  --sup_indices_passive                   []
% 0.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_full_bw                           [BwDemod]
% 0.99/0.98  --sup_immed_triv                        [TrivRules]
% 0.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_immed_bw_main                     []
% 0.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  
% 0.99/0.98  ------ Combination Options
% 0.99/0.98  
% 0.99/0.98  --comb_res_mult                         3
% 0.99/0.98  --comb_sup_mult                         2
% 0.99/0.98  --comb_inst_mult                        10
% 0.99/0.98  
% 0.99/0.98  ------ Debug Options
% 0.99/0.98  
% 0.99/0.98  --dbg_backtrace                         false
% 0.99/0.98  --dbg_dump_prop_clauses                 false
% 0.99/0.98  --dbg_dump_prop_clauses_file            -
% 0.99/0.98  --dbg_out_stat                          false
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  ------ Proving...
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  % SZS status Theorem for theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  fof(f11,axiom,(
% 0.99/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f25,plain,(
% 0.99/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/0.98    inference(nnf_transformation,[],[f11])).
% 0.99/0.98  
% 0.99/0.98  fof(f26,plain,(
% 0.99/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/0.98    inference(flattening,[],[f25])).
% 0.99/0.98  
% 0.99/0.98  fof(f45,plain,(
% 0.99/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.99/0.98    inference(cnf_transformation,[],[f26])).
% 0.99/0.98  
% 0.99/0.98  fof(f70,plain,(
% 0.99/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.99/0.98    inference(equality_resolution,[],[f45])).
% 0.99/0.98  
% 0.99/0.98  fof(f12,axiom,(
% 0.99/0.98    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f46,plain,(
% 0.99/0.98    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.99/0.98    inference(cnf_transformation,[],[f12])).
% 0.99/0.98  
% 0.99/0.98  fof(f2,axiom,(
% 0.99/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f20,plain,(
% 0.99/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.99/0.98    inference(nnf_transformation,[],[f2])).
% 0.99/0.98  
% 0.99/0.98  fof(f21,plain,(
% 0.99/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.99/0.98    inference(rectify,[],[f20])).
% 0.99/0.98  
% 0.99/0.98  fof(f22,plain,(
% 0.99/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f23,plain,(
% 0.99/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 0.99/0.98  
% 0.99/0.98  fof(f30,plain,(
% 0.99/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.99/0.98    inference(cnf_transformation,[],[f23])).
% 0.99/0.98  
% 0.99/0.98  fof(f3,axiom,(
% 0.99/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f34,plain,(
% 0.99/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f3])).
% 0.99/0.98  
% 0.99/0.98  fof(f4,axiom,(
% 0.99/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f35,plain,(
% 0.99/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f4])).
% 0.99/0.98  
% 0.99/0.98  fof(f5,axiom,(
% 0.99/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f36,plain,(
% 0.99/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f5])).
% 0.99/0.98  
% 0.99/0.98  fof(f6,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f37,plain,(
% 0.99/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f6])).
% 0.99/0.98  
% 0.99/0.98  fof(f7,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f38,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f7])).
% 0.99/0.98  
% 0.99/0.98  fof(f8,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f39,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f8])).
% 0.99/0.98  
% 0.99/0.98  fof(f9,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f40,plain,(
% 0.99/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f9])).
% 0.99/0.98  
% 0.99/0.98  fof(f53,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f39,f40])).
% 0.99/0.98  
% 0.99/0.98  fof(f54,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f38,f53])).
% 0.99/0.98  
% 0.99/0.98  fof(f55,plain,(
% 0.99/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f37,f54])).
% 0.99/0.98  
% 0.99/0.98  fof(f56,plain,(
% 0.99/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f36,f55])).
% 0.99/0.98  
% 0.99/0.98  fof(f57,plain,(
% 0.99/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f35,f56])).
% 0.99/0.98  
% 0.99/0.98  fof(f58,plain,(
% 0.99/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.99/0.98    inference(definition_unfolding,[],[f34,f57])).
% 0.99/0.98  
% 0.99/0.98  fof(f62,plain,(
% 0.99/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.99/0.98    inference(definition_unfolding,[],[f30,f58])).
% 0.99/0.98  
% 0.99/0.98  fof(f69,plain,(
% 0.99/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 0.99/0.98    inference(equality_resolution,[],[f62])).
% 0.99/0.98  
% 0.99/0.98  fof(f14,conjecture,(
% 0.99/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f15,negated_conjecture,(
% 0.99/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.99/0.98    inference(negated_conjecture,[],[f14])).
% 0.99/0.98  
% 0.99/0.98  fof(f18,plain,(
% 0.99/0.98    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.99/0.98    inference(ennf_transformation,[],[f15])).
% 0.99/0.98  
% 0.99/0.98  fof(f19,plain,(
% 0.99/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.99/0.98    inference(flattening,[],[f18])).
% 0.99/0.98  
% 0.99/0.98  fof(f27,plain,(
% 0.99/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f28,plain,(
% 0.99/0.98    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 0.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f27])).
% 0.99/0.98  
% 0.99/0.98  fof(f49,plain,(
% 0.99/0.98    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 0.99/0.98    inference(cnf_transformation,[],[f28])).
% 0.99/0.98  
% 0.99/0.98  fof(f66,plain,(
% 0.99/0.98    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.99/0.98    inference(definition_unfolding,[],[f49,f58])).
% 0.99/0.98  
% 0.99/0.98  fof(f13,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f16,plain,(
% 0.99/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.99/0.98    inference(ennf_transformation,[],[f13])).
% 0.99/0.98  
% 0.99/0.98  fof(f17,plain,(
% 0.99/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.99/0.98    inference(flattening,[],[f16])).
% 0.99/0.98  
% 0.99/0.98  fof(f47,plain,(
% 0.99/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f17])).
% 0.99/0.98  
% 0.99/0.98  fof(f50,plain,(
% 0.99/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.99/0.98    inference(cnf_transformation,[],[f28])).
% 0.99/0.98  
% 0.99/0.98  fof(f65,plain,(
% 0.99/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.99/0.98    inference(definition_unfolding,[],[f50,f58])).
% 0.99/0.98  
% 0.99/0.98  fof(f48,plain,(
% 0.99/0.98    v1_funct_1(sK4)),
% 0.99/0.98    inference(cnf_transformation,[],[f28])).
% 0.99/0.98  
% 0.99/0.98  fof(f31,plain,(
% 0.99/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.99/0.98    inference(cnf_transformation,[],[f23])).
% 0.99/0.98  
% 0.99/0.98  fof(f61,plain,(
% 0.99/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.99/0.98    inference(definition_unfolding,[],[f31,f58])).
% 0.99/0.98  
% 0.99/0.98  fof(f67,plain,(
% 0.99/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 0.99/0.98    inference(equality_resolution,[],[f61])).
% 0.99/0.98  
% 0.99/0.98  fof(f68,plain,(
% 0.99/0.98    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 0.99/0.98    inference(equality_resolution,[],[f67])).
% 0.99/0.98  
% 0.99/0.98  fof(f52,plain,(
% 0.99/0.98    k1_funct_1(sK4,sK3) != sK2),
% 0.99/0.98    inference(cnf_transformation,[],[f28])).
% 0.99/0.98  
% 0.99/0.98  fof(f51,plain,(
% 0.99/0.98    r2_hidden(sK3,sK1)),
% 0.99/0.98    inference(cnf_transformation,[],[f28])).
% 0.99/0.98  
% 0.99/0.98  cnf(c_343,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.99/0.98      theory(equality) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_691,plain,
% 0.99/0.98      ( r2_hidden(X0,X1)
% 0.99/0.98      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 0.99/0.98      | X0 != X2
% 0.99/0.98      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_343]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_996,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 0.99/0.98      | r2_hidden(X1,k1_xboole_0)
% 0.99/0.98      | X1 != X0
% 0.99/0.98      | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_691]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_1000,plain,
% 0.99/0.98      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | r2_hidden(sK2,k1_xboole_0)
% 0.99/0.98      | sK2 != sK2
% 0.99/0.98      | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_996]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_7,plain,
% 0.99/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.99/0.98      inference(cnf_transformation,[],[f70]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_10,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 0.99/0.98      inference(cnf_transformation,[],[f46]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_597,plain,
% 0.99/0.98      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 0.99/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_849,plain,
% 0.99/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.99/0.98      inference(superposition,[status(thm)],[c_7,c_597]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_855,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 0.99/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_849]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_857,plain,
% 0.99/0.98      ( ~ r2_hidden(sK2,k1_xboole_0) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_855]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_4,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 0.99/0.98      inference(cnf_transformation,[],[f69]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_701,plain,
% 0.99/0.98      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | k1_funct_1(sK4,sK3) = sK2 ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_15,negated_conjecture,
% 0.99/0.98      ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 0.99/0.98      inference(cnf_transformation,[],[f66]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_11,plain,
% 0.99/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 0.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/0.98      | ~ r2_hidden(X3,X1)
% 0.99/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 0.99/0.98      | ~ v1_funct_1(X0)
% 0.99/0.98      | k1_xboole_0 = X2 ),
% 0.99/0.98      inference(cnf_transformation,[],[f47]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_14,negated_conjecture,
% 0.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
% 0.99/0.98      inference(cnf_transformation,[],[f65]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_184,plain,
% 0.99/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 0.99/0.98      | ~ r2_hidden(X3,X1)
% 0.99/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 0.99/0.98      | ~ v1_funct_1(X0)
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.99/0.98      | sK4 != X0
% 0.99/0.98      | k1_xboole_0 = X2 ),
% 0.99/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_185,plain,
% 0.99/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 0.99/0.98      | ~ r2_hidden(X2,X0)
% 0.99/0.98      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.99/0.98      | ~ v1_funct_1(sK4)
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.99/0.98      | k1_xboole_0 = X1 ),
% 0.99/0.98      inference(unflattening,[status(thm)],[c_184]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_16,negated_conjecture,
% 0.99/0.98      ( v1_funct_1(sK4) ),
% 0.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_189,plain,
% 0.99/0.98      ( r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.99/0.98      | ~ r2_hidden(X2,X0)
% 0.99/0.98      | ~ v1_funct_2(sK4,X0,X1)
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.99/0.98      | k1_xboole_0 = X1 ),
% 0.99/0.98      inference(global_propositional_subsumption,
% 0.99/0.98                [status(thm)],
% 0.99/0.98                [c_185,c_16]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_190,plain,
% 0.99/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 0.99/0.98      | ~ r2_hidden(X2,X0)
% 0.99/0.98      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.99/0.98      | k1_xboole_0 = X1 ),
% 0.99/0.98      inference(renaming,[status(thm)],[c_189]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_217,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,X1)
% 0.99/0.98      | r2_hidden(k1_funct_1(sK4,X0),X2)
% 0.99/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X2
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.99/0.98      | sK1 != X1
% 0.99/0.98      | sK4 != sK4
% 0.99/0.98      | k1_xboole_0 = X2 ),
% 0.99/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_190]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_218,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,sK1)
% 0.99/0.98      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 0.99/0.98      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 0.99/0.98      inference(unflattening,[status(thm)],[c_217]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_249,plain,
% 0.99/0.98      ( ~ r2_hidden(X0,sK1)
% 0.99/0.98      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 0.99/0.98      inference(equality_resolution_simp,[status(thm)],[c_218]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_673,plain,
% 0.99/0.98      ( r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | ~ r2_hidden(sK3,sK1)
% 0.99/0.98      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_249]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_3,plain,
% 0.99/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 0.99/0.98      inference(cnf_transformation,[],[f68]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_40,plain,
% 0.99/0.98      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_37,plain,
% 0.99/0.98      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.99/0.98      | sK2 = sK2 ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_12,negated_conjecture,
% 0.99/0.98      ( k1_funct_1(sK4,sK3) != sK2 ),
% 0.99/0.98      inference(cnf_transformation,[],[f52]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_13,negated_conjecture,
% 0.99/0.98      ( r2_hidden(sK3,sK1) ),
% 0.99/0.98      inference(cnf_transformation,[],[f51]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(contradiction,plain,
% 0.99/0.98      ( $false ),
% 0.99/0.98      inference(minisat,
% 0.99/0.98                [status(thm)],
% 0.99/0.98                [c_1000,c_857,c_701,c_673,c_40,c_37,c_12,c_13]) ).
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  ------                               Statistics
% 0.99/0.98  
% 0.99/0.98  ------ General
% 0.99/0.98  
% 0.99/0.98  abstr_ref_over_cycles:                  0
% 0.99/0.98  abstr_ref_under_cycles:                 0
% 0.99/0.98  gc_basic_clause_elim:                   0
% 0.99/0.98  forced_gc_time:                         0
% 0.99/0.98  parsing_time:                           0.009
% 0.99/0.98  unif_index_cands_time:                  0.
% 0.99/0.98  unif_index_add_time:                    0.
% 0.99/0.98  orderings_time:                         0.
% 0.99/0.98  out_proof_time:                         0.01
% 0.99/0.98  total_time:                             0.064
% 0.99/0.98  num_of_symbols:                         46
% 0.99/0.98  num_of_terms:                           875
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing
% 0.99/0.98  
% 0.99/0.98  num_of_splits:                          0
% 0.99/0.98  num_of_split_atoms:                     0
% 0.99/0.98  num_of_reused_defs:                     0
% 0.99/0.98  num_eq_ax_congr_red:                    6
% 0.99/0.98  num_of_sem_filtered_clauses:            1
% 0.99/0.98  num_of_subtypes:                        0
% 0.99/0.98  monotx_restored_types:                  0
% 0.99/0.98  sat_num_of_epr_types:                   0
% 0.99/0.98  sat_num_of_non_cyclic_types:            0
% 0.99/0.98  sat_guarded_non_collapsed_types:        0
% 0.99/0.98  num_pure_diseq_elim:                    0
% 0.99/0.98  simp_replaced_by:                       0
% 0.99/0.98  res_preprocessed:                       74
% 0.99/0.98  prep_upred:                             0
% 0.99/0.98  prep_unflattend:                        3
% 0.99/0.98  smt_new_axioms:                         0
% 0.99/0.98  pred_elim_cands:                        1
% 0.99/0.98  pred_elim:                              3
% 0.99/0.98  pred_elim_cl:                           3
% 0.99/0.98  pred_elim_cycles:                       5
% 0.99/0.98  merged_defs:                            8
% 0.99/0.98  merged_defs_ncl:                        0
% 0.99/0.98  bin_hyper_res:                          8
% 0.99/0.98  prep_cycles:                            4
% 0.99/0.98  pred_elim_time:                         0.001
% 0.99/0.98  splitting_time:                         0.
% 0.99/0.98  sem_filter_time:                        0.
% 0.99/0.98  monotx_time:                            0.
% 0.99/0.98  subtype_inf_time:                       0.
% 0.99/0.98  
% 0.99/0.98  ------ Problem properties
% 0.99/0.98  
% 0.99/0.98  clauses:                                14
% 0.99/0.98  conjectures:                            2
% 0.99/0.98  epr:                                    1
% 0.99/0.98  horn:                                   11
% 0.99/0.98  ground:                                 2
% 0.99/0.98  unary:                                  7
% 0.99/0.98  binary:                                 3
% 0.99/0.98  lits:                                   25
% 0.99/0.98  lits_eq:                                15
% 0.99/0.98  fd_pure:                                0
% 0.99/0.98  fd_pseudo:                              0
% 0.99/0.98  fd_cond:                                1
% 0.99/0.98  fd_pseudo_cond:                         2
% 0.99/0.98  ac_symbols:                             0
% 0.99/0.98  
% 0.99/0.98  ------ Propositional Solver
% 0.99/0.98  
% 0.99/0.98  prop_solver_calls:                      24
% 0.99/0.98  prop_fast_solver_calls:                 349
% 0.99/0.98  smt_solver_calls:                       0
% 0.99/0.98  smt_fast_solver_calls:                  0
% 0.99/0.98  prop_num_of_clauses:                    280
% 0.99/0.98  prop_preprocess_simplified:             1894
% 0.99/0.98  prop_fo_subsumed:                       3
% 0.99/0.98  prop_solver_time:                       0.
% 0.99/0.98  smt_solver_time:                        0.
% 0.99/0.98  smt_fast_solver_time:                   0.
% 0.99/0.98  prop_fast_solver_time:                  0.
% 0.99/0.98  prop_unsat_core_time:                   0.
% 0.99/0.98  
% 0.99/0.98  ------ QBF
% 0.99/0.98  
% 0.99/0.98  qbf_q_res:                              0
% 0.99/0.98  qbf_num_tautologies:                    0
% 0.99/0.98  qbf_prep_cycles:                        0
% 0.99/0.98  
% 0.99/0.98  ------ BMC1
% 0.99/0.98  
% 0.99/0.98  bmc1_current_bound:                     -1
% 0.99/0.98  bmc1_last_solved_bound:                 -1
% 0.99/0.98  bmc1_unsat_core_size:                   -1
% 0.99/0.98  bmc1_unsat_core_parents_size:           -1
% 0.99/0.98  bmc1_merge_next_fun:                    0
% 0.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.99/0.98  
% 0.99/0.98  ------ Instantiation
% 0.99/0.98  
% 0.99/0.98  inst_num_of_clauses:                    96
% 0.99/0.98  inst_num_in_passive:                    2
% 0.99/0.98  inst_num_in_active:                     51
% 0.99/0.98  inst_num_in_unprocessed:                42
% 0.99/0.98  inst_num_of_loops:                      54
% 0.99/0.98  inst_num_of_learning_restarts:          0
% 0.99/0.98  inst_num_moves_active_passive:          1
% 0.99/0.98  inst_lit_activity:                      0
% 0.99/0.98  inst_lit_activity_moves:                0
% 0.99/0.98  inst_num_tautologies:                   0
% 0.99/0.98  inst_num_prop_implied:                  0
% 0.99/0.98  inst_num_existing_simplified:           0
% 0.99/0.98  inst_num_eq_res_simplified:             0
% 0.99/0.98  inst_num_child_elim:                    0
% 0.99/0.98  inst_num_of_dismatching_blockings:      6
% 0.99/0.98  inst_num_of_non_proper_insts:           59
% 0.99/0.98  inst_num_of_duplicates:                 0
% 0.99/0.98  inst_inst_num_from_inst_to_res:         0
% 0.99/0.98  inst_dismatching_checking_time:         0.
% 0.99/0.98  
% 0.99/0.98  ------ Resolution
% 0.99/0.98  
% 0.99/0.98  res_num_of_clauses:                     0
% 0.99/0.98  res_num_in_passive:                     0
% 0.99/0.98  res_num_in_active:                      0
% 0.99/0.98  res_num_of_loops:                       78
% 0.99/0.98  res_forward_subset_subsumed:            6
% 0.99/0.98  res_backward_subset_subsumed:           0
% 0.99/0.98  res_forward_subsumed:                   0
% 0.99/0.98  res_backward_subsumed:                  0
% 0.99/0.98  res_forward_subsumption_resolution:     0
% 0.99/0.98  res_backward_subsumption_resolution:    0
% 0.99/0.98  res_clause_to_clause_subsumption:       34
% 0.99/0.98  res_orphan_elimination:                 0
% 0.99/0.98  res_tautology_del:                      18
% 0.99/0.98  res_num_eq_res_simplified:              1
% 0.99/0.98  res_num_sel_changes:                    0
% 0.99/0.98  res_moves_from_active_to_pass:          0
% 0.99/0.98  
% 0.99/0.98  ------ Superposition
% 0.99/0.98  
% 0.99/0.98  sup_time_total:                         0.
% 0.99/0.98  sup_time_generating:                    0.
% 0.99/0.98  sup_time_sim_full:                      0.
% 0.99/0.98  sup_time_sim_immed:                     0.
% 0.99/0.98  
% 0.99/0.98  sup_num_of_clauses:                     18
% 0.99/0.98  sup_num_in_active:                      10
% 0.99/0.98  sup_num_in_passive:                     8
% 0.99/0.98  sup_num_of_loops:                       10
% 0.99/0.98  sup_fw_superposition:                   6
% 0.99/0.98  sup_bw_superposition:                   0
% 0.99/0.98  sup_immediate_simplified:               1
% 0.99/0.98  sup_given_eliminated:                   0
% 0.99/0.98  comparisons_done:                       0
% 0.99/0.98  comparisons_avoided:                    0
% 0.99/0.98  
% 0.99/0.98  ------ Simplifications
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  sim_fw_subset_subsumed:                 0
% 0.99/0.98  sim_bw_subset_subsumed:                 0
% 0.99/0.98  sim_fw_subsumed:                        0
% 0.99/0.98  sim_bw_subsumed:                        1
% 0.99/0.98  sim_fw_subsumption_res:                 0
% 0.99/0.98  sim_bw_subsumption_res:                 0
% 0.99/0.98  sim_tautology_del:                      0
% 0.99/0.98  sim_eq_tautology_del:                   0
% 0.99/0.98  sim_eq_res_simp:                        0
% 0.99/0.98  sim_fw_demodulated:                     0
% 0.99/0.98  sim_bw_demodulated:                     0
% 0.99/0.98  sim_light_normalised:                   0
% 0.99/0.98  sim_joinable_taut:                      0
% 0.99/0.98  sim_joinable_simp:                      0
% 0.99/0.98  sim_ac_normalised:                      0
% 0.99/0.98  sim_smt_subsumption:                    0
% 0.99/0.98  
%------------------------------------------------------------------------------
