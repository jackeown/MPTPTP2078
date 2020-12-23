%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:40 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 173 expanded)
%              Number of clauses        :   38 (  44 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  324 ( 774 expanded)
%              Number of equality atoms :  198 ( 512 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X1,X1,X2) = X0
      | k1_enumset1(X2,X2,X2) = X0
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f35,f30,f41,f41,f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f56,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f57,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_enumset1(X1,X1,X2))
      | k1_enumset1(X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f37,f30,f41])).

fof(f63,plain,(
    ! [X2,X1] : r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_enumset1(X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f64,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f6,conjecture,(
    ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,
    ( ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0))
   => k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f21])).

fof(f40,plain,(
    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) != k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f40,f30,f41,f41])).

cnf(c_842,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1328,plain,
    ( X0 != X1
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X1
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = X0 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1581,plain,
    ( X0 != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = X0
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_3805,plain,
    ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_xboole_0
    | k1_xboole_0 != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X2))
    | k1_enumset1(X1,X1,X2) = X0
    | k1_enumset1(X2,X2,X2) = X0
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1541,plain,
    ( ~ r1_tarski(X0,k1_enumset1(sK2,sK2,sK2))
    | k1_enumset1(sK2,sK2,sK2) = X0
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2321,plain,
    ( ~ r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | k1_enumset1(sK2,sK2,sK2) = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | k1_xboole_0 = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_2083,plain,
    ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(X0,X0,X1)
    | k1_enumset1(X0,X0,X1) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_2084,plain,
    ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK2,sK2)
    | k1_enumset1(sK2,sK2,sK2) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_846,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1288,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X0
    | k1_enumset1(sK2,sK2,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1555,plain,
    ( ~ r1_tarski(X0,k1_enumset1(sK2,sK2,sK2))
    | r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X0
    | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_2039,plain,
    ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_xboole_0
    | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_2034,plain,
    ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK2,sK2)
    | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_841,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1548,plain,
    ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1285,plain,
    ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1231,plain,
    ( ~ r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | k1_enumset1(X0,X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1207,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK2,sK2)
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_xboole_0
    | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) != X1
    | k1_enumset1(X0,X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1208,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK2,sK2)
    | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) != X0
    | k1_enumset1(X0,X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1209,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
    | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_xboole_0
    | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_843,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_847,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_43,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) != k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3805,c_2321,c_2084,c_2039,c_2034,c_1548,c_1285,c_1231,c_1207,c_1208,c_1209,c_847,c_43,c_40,c_23,c_20,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:52:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.57/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.97  
% 3.57/0.97  ------  iProver source info
% 3.57/0.97  
% 3.57/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.97  git: non_committed_changes: false
% 3.57/0.97  git: last_make_outside_of_git: false
% 3.57/0.97  
% 3.57/0.97  ------ 
% 3.57/0.97  
% 3.57/0.97  ------ Input Options
% 3.57/0.97  
% 3.57/0.97  --out_options                           all
% 3.57/0.97  --tptp_safe_out                         true
% 3.57/0.97  --problem_path                          ""
% 3.57/0.97  --include_path                          ""
% 3.57/0.97  --clausifier                            res/vclausify_rel
% 3.57/0.97  --clausifier_options                    ""
% 3.57/0.97  --stdin                                 false
% 3.57/0.97  --stats_out                             all
% 3.57/0.97  
% 3.57/0.97  ------ General Options
% 3.57/0.97  
% 3.57/0.97  --fof                                   false
% 3.57/0.97  --time_out_real                         305.
% 3.57/0.97  --time_out_virtual                      -1.
% 3.57/0.97  --symbol_type_check                     false
% 3.57/0.97  --clausify_out                          false
% 3.57/0.97  --sig_cnt_out                           false
% 3.57/0.97  --trig_cnt_out                          false
% 3.57/0.97  --trig_cnt_out_tolerance                1.
% 3.57/0.97  --trig_cnt_out_sk_spl                   false
% 3.57/0.97  --abstr_cl_out                          false
% 3.57/0.97  
% 3.57/0.97  ------ Global Options
% 3.57/0.97  
% 3.57/0.97  --schedule                              default
% 3.57/0.97  --add_important_lit                     false
% 3.57/0.97  --prop_solver_per_cl                    1000
% 3.57/0.97  --min_unsat_core                        false
% 3.57/0.97  --soft_assumptions                      false
% 3.57/0.97  --soft_lemma_size                       3
% 3.57/0.97  --prop_impl_unit_size                   0
% 3.57/0.97  --prop_impl_unit                        []
% 3.57/0.97  --share_sel_clauses                     true
% 3.57/0.97  --reset_solvers                         false
% 3.57/0.97  --bc_imp_inh                            [conj_cone]
% 3.57/0.97  --conj_cone_tolerance                   3.
% 3.57/0.97  --extra_neg_conj                        none
% 3.57/0.97  --large_theory_mode                     true
% 3.57/0.97  --prolific_symb_bound                   200
% 3.57/0.97  --lt_threshold                          2000
% 3.57/0.97  --clause_weak_htbl                      true
% 3.57/0.97  --gc_record_bc_elim                     false
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing Options
% 3.57/0.97  
% 3.57/0.97  --preprocessing_flag                    true
% 3.57/0.97  --time_out_prep_mult                    0.1
% 3.57/0.97  --splitting_mode                        input
% 3.57/0.97  --splitting_grd                         true
% 3.57/0.97  --splitting_cvd                         false
% 3.57/0.97  --splitting_cvd_svl                     false
% 3.57/0.97  --splitting_nvd                         32
% 3.57/0.97  --sub_typing                            true
% 3.57/0.97  --prep_gs_sim                           true
% 3.57/0.97  --prep_unflatten                        true
% 3.57/0.97  --prep_res_sim                          true
% 3.57/0.97  --prep_upred                            true
% 3.57/0.97  --prep_sem_filter                       exhaustive
% 3.57/0.97  --prep_sem_filter_out                   false
% 3.57/0.97  --pred_elim                             true
% 3.57/0.97  --res_sim_input                         true
% 3.57/0.97  --eq_ax_congr_red                       true
% 3.57/0.97  --pure_diseq_elim                       true
% 3.57/0.97  --brand_transform                       false
% 3.57/0.97  --non_eq_to_eq                          false
% 3.57/0.97  --prep_def_merge                        true
% 3.57/0.97  --prep_def_merge_prop_impl              false
% 3.57/0.97  --prep_def_merge_mbd                    true
% 3.57/0.97  --prep_def_merge_tr_red                 false
% 3.57/0.97  --prep_def_merge_tr_cl                  false
% 3.57/0.97  --smt_preprocessing                     true
% 3.57/0.97  --smt_ac_axioms                         fast
% 3.57/0.97  --preprocessed_out                      false
% 3.57/0.97  --preprocessed_stats                    false
% 3.57/0.97  
% 3.57/0.97  ------ Abstraction refinement Options
% 3.57/0.97  
% 3.57/0.97  --abstr_ref                             []
% 3.57/0.97  --abstr_ref_prep                        false
% 3.57/0.97  --abstr_ref_until_sat                   false
% 3.57/0.97  --abstr_ref_sig_restrict                funpre
% 3.57/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.97  --abstr_ref_under                       []
% 3.57/0.97  
% 3.57/0.97  ------ SAT Options
% 3.57/0.97  
% 3.57/0.97  --sat_mode                              false
% 3.57/0.97  --sat_fm_restart_options                ""
% 3.57/0.97  --sat_gr_def                            false
% 3.57/0.97  --sat_epr_types                         true
% 3.57/0.97  --sat_non_cyclic_types                  false
% 3.57/0.97  --sat_finite_models                     false
% 3.57/0.97  --sat_fm_lemmas                         false
% 3.57/0.97  --sat_fm_prep                           false
% 3.57/0.97  --sat_fm_uc_incr                        true
% 3.57/0.97  --sat_out_model                         small
% 3.57/0.97  --sat_out_clauses                       false
% 3.57/0.97  
% 3.57/0.97  ------ QBF Options
% 3.57/0.97  
% 3.57/0.97  --qbf_mode                              false
% 3.57/0.97  --qbf_elim_univ                         false
% 3.57/0.97  --qbf_dom_inst                          none
% 3.57/0.97  --qbf_dom_pre_inst                      false
% 3.57/0.97  --qbf_sk_in                             false
% 3.57/0.97  --qbf_pred_elim                         true
% 3.57/0.97  --qbf_split                             512
% 3.57/0.97  
% 3.57/0.97  ------ BMC1 Options
% 3.57/0.97  
% 3.57/0.97  --bmc1_incremental                      false
% 3.57/0.97  --bmc1_axioms                           reachable_all
% 3.57/0.97  --bmc1_min_bound                        0
% 3.57/0.97  --bmc1_max_bound                        -1
% 3.57/0.97  --bmc1_max_bound_default                -1
% 3.57/0.97  --bmc1_symbol_reachability              true
% 3.57/0.97  --bmc1_property_lemmas                  false
% 3.57/0.97  --bmc1_k_induction                      false
% 3.57/0.97  --bmc1_non_equiv_states                 false
% 3.57/0.97  --bmc1_deadlock                         false
% 3.57/0.97  --bmc1_ucm                              false
% 3.57/0.97  --bmc1_add_unsat_core                   none
% 3.57/0.97  --bmc1_unsat_core_children              false
% 3.57/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.97  --bmc1_out_stat                         full
% 3.57/0.97  --bmc1_ground_init                      false
% 3.57/0.97  --bmc1_pre_inst_next_state              false
% 3.57/0.97  --bmc1_pre_inst_state                   false
% 3.57/0.97  --bmc1_pre_inst_reach_state             false
% 3.57/0.97  --bmc1_out_unsat_core                   false
% 3.57/0.97  --bmc1_aig_witness_out                  false
% 3.57/0.97  --bmc1_verbose                          false
% 3.57/0.97  --bmc1_dump_clauses_tptp                false
% 3.57/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.97  --bmc1_dump_file                        -
% 3.57/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.97  --bmc1_ucm_extend_mode                  1
% 3.57/0.97  --bmc1_ucm_init_mode                    2
% 3.57/0.97  --bmc1_ucm_cone_mode                    none
% 3.57/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.97  --bmc1_ucm_relax_model                  4
% 3.57/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.97  --bmc1_ucm_layered_model                none
% 3.57/0.97  --bmc1_ucm_max_lemma_size               10
% 3.57/0.97  
% 3.57/0.97  ------ AIG Options
% 3.57/0.97  
% 3.57/0.97  --aig_mode                              false
% 3.57/0.97  
% 3.57/0.97  ------ Instantiation Options
% 3.57/0.97  
% 3.57/0.97  --instantiation_flag                    true
% 3.57/0.97  --inst_sos_flag                         true
% 3.57/0.97  --inst_sos_phase                        true
% 3.57/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.97  --inst_lit_sel_side                     num_symb
% 3.57/0.97  --inst_solver_per_active                1400
% 3.57/0.97  --inst_solver_calls_frac                1.
% 3.57/0.97  --inst_passive_queue_type               priority_queues
% 3.57/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.97  --inst_passive_queues_freq              [25;2]
% 3.57/0.97  --inst_dismatching                      true
% 3.57/0.97  --inst_eager_unprocessed_to_passive     true
% 3.57/0.97  --inst_prop_sim_given                   true
% 3.57/0.97  --inst_prop_sim_new                     false
% 3.57/0.97  --inst_subs_new                         false
% 3.57/0.97  --inst_eq_res_simp                      false
% 3.57/0.97  --inst_subs_given                       false
% 3.57/0.97  --inst_orphan_elimination               true
% 3.57/0.97  --inst_learning_loop_flag               true
% 3.57/0.97  --inst_learning_start                   3000
% 3.57/0.97  --inst_learning_factor                  2
% 3.57/0.97  --inst_start_prop_sim_after_learn       3
% 3.57/0.97  --inst_sel_renew                        solver
% 3.57/0.97  --inst_lit_activity_flag                true
% 3.57/0.97  --inst_restr_to_given                   false
% 3.57/0.97  --inst_activity_threshold               500
% 3.57/0.97  --inst_out_proof                        true
% 3.57/0.97  
% 3.57/0.97  ------ Resolution Options
% 3.57/0.97  
% 3.57/0.97  --resolution_flag                       true
% 3.57/0.97  --res_lit_sel                           adaptive
% 3.57/0.97  --res_lit_sel_side                      none
% 3.57/0.97  --res_ordering                          kbo
% 3.57/0.97  --res_to_prop_solver                    active
% 3.57/0.97  --res_prop_simpl_new                    false
% 3.57/0.97  --res_prop_simpl_given                  true
% 3.57/0.97  --res_passive_queue_type                priority_queues
% 3.57/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.97  --res_passive_queues_freq               [15;5]
% 3.57/0.97  --res_forward_subs                      full
% 3.57/0.97  --res_backward_subs                     full
% 3.57/0.97  --res_forward_subs_resolution           true
% 3.57/0.97  --res_backward_subs_resolution          true
% 3.57/0.97  --res_orphan_elimination                true
% 3.57/0.97  --res_time_limit                        2.
% 3.57/0.97  --res_out_proof                         true
% 3.57/0.97  
% 3.57/0.97  ------ Superposition Options
% 3.57/0.97  
% 3.57/0.97  --superposition_flag                    true
% 3.57/0.97  --sup_passive_queue_type                priority_queues
% 3.57/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.97  --demod_completeness_check              fast
% 3.57/0.97  --demod_use_ground                      true
% 3.57/0.97  --sup_to_prop_solver                    passive
% 3.57/0.97  --sup_prop_simpl_new                    true
% 3.57/0.97  --sup_prop_simpl_given                  true
% 3.57/0.97  --sup_fun_splitting                     true
% 3.57/0.97  --sup_smt_interval                      50000
% 3.57/0.97  
% 3.57/0.97  ------ Superposition Simplification Setup
% 3.57/0.97  
% 3.57/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.97  --sup_immed_triv                        [TrivRules]
% 3.57/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_immed_bw_main                     []
% 3.57/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_input_bw                          []
% 3.57/0.97  
% 3.57/0.97  ------ Combination Options
% 3.57/0.97  
% 3.57/0.97  --comb_res_mult                         3
% 3.57/0.97  --comb_sup_mult                         2
% 3.57/0.97  --comb_inst_mult                        10
% 3.57/0.97  
% 3.57/0.97  ------ Debug Options
% 3.57/0.97  
% 3.57/0.97  --dbg_backtrace                         false
% 3.57/0.97  --dbg_dump_prop_clauses                 false
% 3.57/0.97  --dbg_dump_prop_clauses_file            -
% 3.57/0.97  --dbg_out_stat                          false
% 3.57/0.97  ------ Parsing...
% 3.57/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.97  ------ Proving...
% 3.57/0.97  ------ Problem Properties 
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  clauses                                 16
% 3.57/0.97  conjectures                             1
% 3.57/0.97  EPR                                     0
% 3.57/0.97  Horn                                    12
% 3.57/0.97  unary                                   7
% 3.57/0.97  binary                                  2
% 3.57/0.97  lits                                    35
% 3.57/0.97  lits eq                                 16
% 3.57/0.97  fd_pure                                 0
% 3.57/0.97  fd_pseudo                               0
% 3.57/0.97  fd_cond                                 0
% 3.57/0.97  fd_pseudo_cond                          6
% 3.57/0.97  AC symbols                              0
% 3.57/0.97  
% 3.57/0.97  ------ Schedule dynamic 5 is on 
% 3.57/0.97  
% 3.57/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  ------ 
% 3.57/0.97  Current options:
% 3.57/0.97  ------ 
% 3.57/0.97  
% 3.57/0.97  ------ Input Options
% 3.57/0.97  
% 3.57/0.97  --out_options                           all
% 3.57/0.97  --tptp_safe_out                         true
% 3.57/0.97  --problem_path                          ""
% 3.57/0.97  --include_path                          ""
% 3.57/0.97  --clausifier                            res/vclausify_rel
% 3.57/0.97  --clausifier_options                    ""
% 3.57/0.97  --stdin                                 false
% 3.57/0.97  --stats_out                             all
% 3.57/0.97  
% 3.57/0.97  ------ General Options
% 3.57/0.97  
% 3.57/0.97  --fof                                   false
% 3.57/0.97  --time_out_real                         305.
% 3.57/0.97  --time_out_virtual                      -1.
% 3.57/0.97  --symbol_type_check                     false
% 3.57/0.97  --clausify_out                          false
% 3.57/0.97  --sig_cnt_out                           false
% 3.57/0.97  --trig_cnt_out                          false
% 3.57/0.97  --trig_cnt_out_tolerance                1.
% 3.57/0.97  --trig_cnt_out_sk_spl                   false
% 3.57/0.97  --abstr_cl_out                          false
% 3.57/0.97  
% 3.57/0.97  ------ Global Options
% 3.57/0.97  
% 3.57/0.97  --schedule                              default
% 3.57/0.97  --add_important_lit                     false
% 3.57/0.97  --prop_solver_per_cl                    1000
% 3.57/0.97  --min_unsat_core                        false
% 3.57/0.97  --soft_assumptions                      false
% 3.57/0.97  --soft_lemma_size                       3
% 3.57/0.97  --prop_impl_unit_size                   0
% 3.57/0.97  --prop_impl_unit                        []
% 3.57/0.97  --share_sel_clauses                     true
% 3.57/0.97  --reset_solvers                         false
% 3.57/0.97  --bc_imp_inh                            [conj_cone]
% 3.57/0.97  --conj_cone_tolerance                   3.
% 3.57/0.97  --extra_neg_conj                        none
% 3.57/0.97  --large_theory_mode                     true
% 3.57/0.97  --prolific_symb_bound                   200
% 3.57/0.97  --lt_threshold                          2000
% 3.57/0.97  --clause_weak_htbl                      true
% 3.57/0.97  --gc_record_bc_elim                     false
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing Options
% 3.57/0.97  
% 3.57/0.97  --preprocessing_flag                    true
% 3.57/0.97  --time_out_prep_mult                    0.1
% 3.57/0.97  --splitting_mode                        input
% 3.57/0.97  --splitting_grd                         true
% 3.57/0.97  --splitting_cvd                         false
% 3.57/0.97  --splitting_cvd_svl                     false
% 3.57/0.97  --splitting_nvd                         32
% 3.57/0.97  --sub_typing                            true
% 3.57/0.97  --prep_gs_sim                           true
% 3.57/0.97  --prep_unflatten                        true
% 3.57/0.97  --prep_res_sim                          true
% 3.57/0.97  --prep_upred                            true
% 3.57/0.97  --prep_sem_filter                       exhaustive
% 3.57/0.97  --prep_sem_filter_out                   false
% 3.57/0.97  --pred_elim                             true
% 3.57/0.97  --res_sim_input                         true
% 3.57/0.97  --eq_ax_congr_red                       true
% 3.57/0.97  --pure_diseq_elim                       true
% 3.57/0.97  --brand_transform                       false
% 3.57/0.97  --non_eq_to_eq                          false
% 3.57/0.97  --prep_def_merge                        true
% 3.57/0.97  --prep_def_merge_prop_impl              false
% 3.57/0.97  --prep_def_merge_mbd                    true
% 3.57/0.97  --prep_def_merge_tr_red                 false
% 3.57/0.97  --prep_def_merge_tr_cl                  false
% 3.57/0.97  --smt_preprocessing                     true
% 3.57/0.97  --smt_ac_axioms                         fast
% 3.57/0.97  --preprocessed_out                      false
% 3.57/0.97  --preprocessed_stats                    false
% 3.57/0.97  
% 3.57/0.97  ------ Abstraction refinement Options
% 3.57/0.97  
% 3.57/0.97  --abstr_ref                             []
% 3.57/0.97  --abstr_ref_prep                        false
% 3.57/0.97  --abstr_ref_until_sat                   false
% 3.57/0.97  --abstr_ref_sig_restrict                funpre
% 3.57/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.97  --abstr_ref_under                       []
% 3.57/0.97  
% 3.57/0.97  ------ SAT Options
% 3.57/0.97  
% 3.57/0.97  --sat_mode                              false
% 3.57/0.97  --sat_fm_restart_options                ""
% 3.57/0.97  --sat_gr_def                            false
% 3.57/0.97  --sat_epr_types                         true
% 3.57/0.97  --sat_non_cyclic_types                  false
% 3.57/0.97  --sat_finite_models                     false
% 3.57/0.97  --sat_fm_lemmas                         false
% 3.57/0.97  --sat_fm_prep                           false
% 3.57/0.97  --sat_fm_uc_incr                        true
% 3.57/0.97  --sat_out_model                         small
% 3.57/0.97  --sat_out_clauses                       false
% 3.57/0.97  
% 3.57/0.97  ------ QBF Options
% 3.57/0.97  
% 3.57/0.97  --qbf_mode                              false
% 3.57/0.97  --qbf_elim_univ                         false
% 3.57/0.97  --qbf_dom_inst                          none
% 3.57/0.97  --qbf_dom_pre_inst                      false
% 3.57/0.97  --qbf_sk_in                             false
% 3.57/0.97  --qbf_pred_elim                         true
% 3.57/0.97  --qbf_split                             512
% 3.57/0.97  
% 3.57/0.97  ------ BMC1 Options
% 3.57/0.97  
% 3.57/0.97  --bmc1_incremental                      false
% 3.57/0.97  --bmc1_axioms                           reachable_all
% 3.57/0.97  --bmc1_min_bound                        0
% 3.57/0.97  --bmc1_max_bound                        -1
% 3.57/0.97  --bmc1_max_bound_default                -1
% 3.57/0.97  --bmc1_symbol_reachability              true
% 3.57/0.97  --bmc1_property_lemmas                  false
% 3.57/0.97  --bmc1_k_induction                      false
% 3.57/0.97  --bmc1_non_equiv_states                 false
% 3.57/0.97  --bmc1_deadlock                         false
% 3.57/0.97  --bmc1_ucm                              false
% 3.57/0.97  --bmc1_add_unsat_core                   none
% 3.57/0.97  --bmc1_unsat_core_children              false
% 3.57/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.97  --bmc1_out_stat                         full
% 3.57/0.97  --bmc1_ground_init                      false
% 3.57/0.97  --bmc1_pre_inst_next_state              false
% 3.57/0.97  --bmc1_pre_inst_state                   false
% 3.57/0.97  --bmc1_pre_inst_reach_state             false
% 3.57/0.97  --bmc1_out_unsat_core                   false
% 3.57/0.97  --bmc1_aig_witness_out                  false
% 3.57/0.97  --bmc1_verbose                          false
% 3.57/0.97  --bmc1_dump_clauses_tptp                false
% 3.57/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.97  --bmc1_dump_file                        -
% 3.57/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.97  --bmc1_ucm_extend_mode                  1
% 3.57/0.97  --bmc1_ucm_init_mode                    2
% 3.57/0.97  --bmc1_ucm_cone_mode                    none
% 3.57/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.97  --bmc1_ucm_relax_model                  4
% 3.57/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.97  --bmc1_ucm_layered_model                none
% 3.57/0.97  --bmc1_ucm_max_lemma_size               10
% 3.57/0.97  
% 3.57/0.97  ------ AIG Options
% 3.57/0.97  
% 3.57/0.97  --aig_mode                              false
% 3.57/0.97  
% 3.57/0.97  ------ Instantiation Options
% 3.57/0.97  
% 3.57/0.97  --instantiation_flag                    true
% 3.57/0.97  --inst_sos_flag                         true
% 3.57/0.97  --inst_sos_phase                        true
% 3.57/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.97  --inst_lit_sel_side                     none
% 3.57/0.97  --inst_solver_per_active                1400
% 3.57/0.97  --inst_solver_calls_frac                1.
% 3.57/0.97  --inst_passive_queue_type               priority_queues
% 3.57/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.97  --inst_passive_queues_freq              [25;2]
% 3.57/0.97  --inst_dismatching                      true
% 3.57/0.97  --inst_eager_unprocessed_to_passive     true
% 3.57/0.97  --inst_prop_sim_given                   true
% 3.57/0.97  --inst_prop_sim_new                     false
% 3.57/0.97  --inst_subs_new                         false
% 3.57/0.97  --inst_eq_res_simp                      false
% 3.57/0.97  --inst_subs_given                       false
% 3.57/0.97  --inst_orphan_elimination               true
% 3.57/0.97  --inst_learning_loop_flag               true
% 3.57/0.97  --inst_learning_start                   3000
% 3.57/0.97  --inst_learning_factor                  2
% 3.57/0.97  --inst_start_prop_sim_after_learn       3
% 3.57/0.97  --inst_sel_renew                        solver
% 3.57/0.97  --inst_lit_activity_flag                true
% 3.57/0.97  --inst_restr_to_given                   false
% 3.57/0.97  --inst_activity_threshold               500
% 3.57/0.97  --inst_out_proof                        true
% 3.57/0.97  
% 3.57/0.97  ------ Resolution Options
% 3.57/0.97  
% 3.57/0.97  --resolution_flag                       false
% 3.57/0.97  --res_lit_sel                           adaptive
% 3.57/0.97  --res_lit_sel_side                      none
% 3.57/0.97  --res_ordering                          kbo
% 3.57/0.97  --res_to_prop_solver                    active
% 3.57/0.97  --res_prop_simpl_new                    false
% 3.57/0.97  --res_prop_simpl_given                  true
% 3.57/0.97  --res_passive_queue_type                priority_queues
% 3.57/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.97  --res_passive_queues_freq               [15;5]
% 3.57/0.97  --res_forward_subs                      full
% 3.57/0.97  --res_backward_subs                     full
% 3.57/0.97  --res_forward_subs_resolution           true
% 3.57/0.97  --res_backward_subs_resolution          true
% 3.57/0.97  --res_orphan_elimination                true
% 3.57/0.97  --res_time_limit                        2.
% 3.57/0.97  --res_out_proof                         true
% 3.57/0.97  
% 3.57/0.97  ------ Superposition Options
% 3.57/0.97  
% 3.57/0.97  --superposition_flag                    true
% 3.57/0.97  --sup_passive_queue_type                priority_queues
% 3.57/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.97  --demod_completeness_check              fast
% 3.57/0.97  --demod_use_ground                      true
% 3.57/0.97  --sup_to_prop_solver                    passive
% 3.57/0.97  --sup_prop_simpl_new                    true
% 3.57/0.97  --sup_prop_simpl_given                  true
% 3.57/0.97  --sup_fun_splitting                     true
% 3.57/0.97  --sup_smt_interval                      50000
% 3.57/0.97  
% 3.57/0.97  ------ Superposition Simplification Setup
% 3.57/0.97  
% 3.57/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.97  --sup_immed_triv                        [TrivRules]
% 3.57/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_immed_bw_main                     []
% 3.57/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.97  --sup_input_bw                          []
% 3.57/0.97  
% 3.57/0.97  ------ Combination Options
% 3.57/0.97  
% 3.57/0.97  --comb_res_mult                         3
% 3.57/0.97  --comb_sup_mult                         2
% 3.57/0.97  --comb_inst_mult                        10
% 3.57/0.97  
% 3.57/0.97  ------ Debug Options
% 3.57/0.97  
% 3.57/0.97  --dbg_backtrace                         false
% 3.57/0.97  --dbg_dump_prop_clauses                 false
% 3.57/0.97  --dbg_dump_prop_clauses_file            -
% 3.57/0.97  --dbg_out_stat                          false
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  ------ Proving...
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  % SZS status Theorem for theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  fof(f5,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f8,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.57/0.97    inference(ennf_transformation,[],[f5])).
% 3.57/0.97  
% 3.57/0.97  fof(f19,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.57/0.97    inference(nnf_transformation,[],[f8])).
% 3.57/0.97  
% 3.57/0.97  fof(f20,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.57/0.97    inference(flattening,[],[f19])).
% 3.57/0.97  
% 3.57/0.97  fof(f35,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f20])).
% 3.57/0.97  
% 3.57/0.97  fof(f2,axiom,(
% 3.57/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f29,plain,(
% 3.57/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f2])).
% 3.57/0.97  
% 3.57/0.97  fof(f41,plain,(
% 3.57/0.97    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.57/0.97    inference(definition_unfolding,[],[f29,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f3,axiom,(
% 3.57/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f30,plain,(
% 3.57/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f3])).
% 3.57/0.97  
% 3.57/0.97  fof(f52,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X1,X1,X2) = X0 | k1_enumset1(X2,X2,X2) = X0 | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X2))) )),
% 3.57/0.97    inference(definition_unfolding,[],[f35,f30,f41,f41,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f4,axiom,(
% 3.57/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f15,plain,(
% 3.57/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.97    inference(nnf_transformation,[],[f4])).
% 3.57/0.97  
% 3.57/0.97  fof(f16,plain,(
% 3.57/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.97    inference(rectify,[],[f15])).
% 3.57/0.97  
% 3.57/0.97  fof(f17,plain,(
% 3.57/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f18,plain,(
% 3.57/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 3.57/0.97  
% 3.57/0.97  fof(f31,plain,(
% 3.57/0.97    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.57/0.97    inference(cnf_transformation,[],[f18])).
% 3.57/0.97  
% 3.57/0.97  fof(f60,plain,(
% 3.57/0.97    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.57/0.97    inference(equality_resolution,[],[f31])).
% 3.57/0.97  
% 3.57/0.97  fof(f32,plain,(
% 3.57/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.57/0.97    inference(cnf_transformation,[],[f18])).
% 3.57/0.97  
% 3.57/0.97  fof(f59,plain,(
% 3.57/0.97    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.57/0.97    inference(equality_resolution,[],[f32])).
% 3.57/0.97  
% 3.57/0.97  fof(f1,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f10,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.57/0.97    inference(nnf_transformation,[],[f1])).
% 3.57/0.97  
% 3.57/0.97  fof(f11,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.57/0.97    inference(flattening,[],[f10])).
% 3.57/0.97  
% 3.57/0.97  fof(f12,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.57/0.97    inference(rectify,[],[f11])).
% 3.57/0.97  
% 3.57/0.97  fof(f13,plain,(
% 3.57/0.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f14,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 3.57/0.97  
% 3.57/0.97  fof(f26,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f44,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(definition_unfolding,[],[f26,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f28,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f42,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(definition_unfolding,[],[f28,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f27,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f43,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.57/0.97    inference(definition_unfolding,[],[f27,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f24,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.57/0.97    inference(cnf_transformation,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f46,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.57/0.97    inference(definition_unfolding,[],[f24,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f56,plain,(
% 3.57/0.97    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.57/0.97    inference(equality_resolution,[],[f46])).
% 3.57/0.97  
% 3.57/0.97  fof(f57,plain,(
% 3.57/0.97    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.57/0.97    inference(equality_resolution,[],[f56])).
% 3.57/0.97  
% 3.57/0.97  fof(f23,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.57/0.97    inference(cnf_transformation,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f47,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.57/0.97    inference(definition_unfolding,[],[f23,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f58,plain,(
% 3.57/0.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 3.57/0.97    inference(equality_resolution,[],[f47])).
% 3.57/0.97  
% 3.57/0.97  fof(f37,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.57/0.97    inference(cnf_transformation,[],[f20])).
% 3.57/0.97  
% 3.57/0.97  fof(f50,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_enumset1(X1,X1,X2)) | k1_enumset1(X1,X1,X1) != X0) )),
% 3.57/0.97    inference(definition_unfolding,[],[f37,f30,f41])).
% 3.57/0.97  
% 3.57/0.97  fof(f63,plain,(
% 3.57/0.97    ( ! [X2,X1] : (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2))) )),
% 3.57/0.97    inference(equality_resolution,[],[f50])).
% 3.57/0.97  
% 3.57/0.97  fof(f36,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 3.57/0.97    inference(cnf_transformation,[],[f20])).
% 3.57/0.97  
% 3.57/0.97  fof(f51,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_enumset1(X1,X1,X2)) | k1_xboole_0 != X0) )),
% 3.57/0.97    inference(definition_unfolding,[],[f36,f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f64,plain,(
% 3.57/0.97    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X2))) )),
% 3.57/0.97    inference(equality_resolution,[],[f51])).
% 3.57/0.97  
% 3.57/0.97  fof(f6,conjecture,(
% 3.57/0.97    ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f7,negated_conjecture,(
% 3.57/0.97    ~! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0))),
% 3.57/0.97    inference(negated_conjecture,[],[f6])).
% 3.57/0.97  
% 3.57/0.97  fof(f9,plain,(
% 3.57/0.97    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0))),
% 3.57/0.97    inference(ennf_transformation,[],[f7])).
% 3.57/0.97  
% 3.57/0.97  fof(f21,plain,(
% 3.57/0.97    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0)) => k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f22,plain,(
% 3.57/0.97    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f21])).
% 3.57/0.97  
% 3.57/0.97  fof(f40,plain,(
% 3.57/0.97    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.57/0.97    inference(cnf_transformation,[],[f22])).
% 3.57/0.97  
% 3.57/0.97  fof(f53,plain,(
% 3.57/0.97    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) != k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),
% 3.57/0.97    inference(definition_unfolding,[],[f40,f30,f41,f41])).
% 3.57/0.97  
% 3.57/0.97  cnf(c_842,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1328,plain,
% 3.57/0.97      ( X0 != X1
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X1
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = X0 ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_842]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1581,plain,
% 3.57/0.97      ( X0 != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = X0
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_1328]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_3805,plain,
% 3.57/0.97      ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_xboole_0
% 3.57/0.97      | k1_xboole_0 != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_1581]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_14,plain,
% 3.57/0.97      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X2))
% 3.57/0.97      | k1_enumset1(X1,X1,X2) = X0
% 3.57/0.97      | k1_enumset1(X2,X2,X2) = X0
% 3.57/0.97      | k1_enumset1(X1,X1,X1) = X0
% 3.57/0.97      | k1_xboole_0 = X0 ),
% 3.57/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1541,plain,
% 3.57/0.97      ( ~ r1_tarski(X0,k1_enumset1(sK2,sK2,sK2))
% 3.57/0.97      | k1_enumset1(sK2,sK2,sK2) = X0
% 3.57/0.97      | k1_xboole_0 = X0 ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_2321,plain,
% 3.57/0.97      ( ~ r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.97      | k1_enumset1(sK2,sK2,sK2) = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.97      | k1_xboole_0 = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_1541]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_2083,plain,
% 3.57/0.97      ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(X0,X0,X1)
% 3.57/0.97      | k1_enumset1(X0,X0,X1) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_1581]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_2084,plain,
% 3.57/0.97      ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK2,sK2)
% 3.57/0.97      | k1_enumset1(sK2,sK2,sK2) != sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_2083]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_846,plain,
% 3.57/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.57/0.97      theory(equality) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1288,plain,
% 3.57/0.97      ( ~ r1_tarski(X0,X1)
% 3.57/0.97      | r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.97      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X0
% 3.57/0.97      | k1_enumset1(sK2,sK2,sK2) != X1 ),
% 3.57/0.97      inference(instantiation,[status(thm)],[c_846]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1555,plain,
% 3.57/0.97      ( ~ r1_tarski(X0,k1_enumset1(sK2,sK2,sK2))
% 3.57/0.97      | r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != X0
% 3.57/0.98      | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1288]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2039,plain,
% 3.57/0.98      ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_xboole_0
% 3.57/0.98      | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1555]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2034,plain,
% 3.57/0.98      ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK2,sK2)
% 3.57/0.98      | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1555]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_841,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1548,plain,
% 3.57/0.98      ( sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_841]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_9,plain,
% 3.57/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1285,plain,
% 3.57/0.98      ( r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_8,plain,
% 3.57/0.98      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1231,plain,
% 3.57/0.98      ( ~ r1_tarski(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_enumset1(sK2,sK2,sK2))
% 3.57/0.98      | r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1,X2),X2)
% 3.57/0.98      | sK0(X0,X1,X2) = X1
% 3.57/0.98      | sK0(X0,X1,X2) = X0
% 3.57/0.98      | k1_enumset1(X0,X0,X1) = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1207,plain,
% 3.57/0.98      ( r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_enumset1(sK2,sK2,sK2)
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = k1_xboole_0
% 3.57/0.98      | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_0,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.57/0.98      | sK0(X0,X1,X2) != X1
% 3.57/0.98      | k1_enumset1(X0,X0,X1) = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1208,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_enumset1(sK2,sK2,sK2)
% 3.57/0.98      | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.57/0.98      | sK0(X0,X1,X2) != X0
% 3.57/0.98      | k1_enumset1(X0,X0,X1) = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1209,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)))
% 3.57/0.98      | sK0(k1_xboole_0,k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) != k1_xboole_0
% 3.57/0.98      | k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) = k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_843,plain,
% 3.57/0.98      ( X0 != X1
% 3.57/0.98      | X2 != X3
% 3.57/0.98      | X4 != X5
% 3.57/0.98      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 3.57/0.98      theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_847,plain,
% 3.57/0.98      ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
% 3.57/0.98      | sK2 != sK2 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_843]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_43,plain,
% 3.57/0.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_40,plain,
% 3.57/0.98      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | sK2 = sK2 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_12,plain,
% 3.57/0.98      ( r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_23,plain,
% 3.57/0.98      ( r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_13,plain,
% 3.57/0.98      ( r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_20,plain,
% 3.57/0.98      ( r1_tarski(k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_15,negated_conjecture,
% 3.57/0.98      ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(sK2,sK2,sK2)) != k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(contradiction,plain,
% 3.57/0.98      ( $false ),
% 3.57/0.98      inference(minisat,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3805,c_2321,c_2084,c_2039,c_2034,c_1548,c_1285,c_1231,
% 3.57/0.98                 c_1207,c_1208,c_1209,c_847,c_43,c_40,c_23,c_20,c_15]) ).
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  ------                               Statistics
% 3.57/0.98  
% 3.57/0.98  ------ General
% 3.57/0.98  
% 3.57/0.98  abstr_ref_over_cycles:                  0
% 3.57/0.98  abstr_ref_under_cycles:                 0
% 3.57/0.98  gc_basic_clause_elim:                   0
% 3.57/0.98  forced_gc_time:                         0
% 3.57/0.98  parsing_time:                           0.009
% 3.57/0.98  unif_index_cands_time:                  0.
% 3.57/0.98  unif_index_add_time:                    0.
% 3.57/0.98  orderings_time:                         0.
% 3.57/0.98  out_proof_time:                         0.008
% 3.57/0.98  total_time:                             0.186
% 3.57/0.98  num_of_symbols:                         39
% 3.57/0.98  num_of_terms:                           4399
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing
% 3.57/0.98  
% 3.57/0.98  num_of_splits:                          0
% 3.57/0.98  num_of_split_atoms:                     0
% 3.57/0.98  num_of_reused_defs:                     0
% 3.57/0.98  num_eq_ax_congr_red:                    10
% 3.57/0.98  num_of_sem_filtered_clauses:            1
% 3.57/0.98  num_of_subtypes:                        0
% 3.57/0.98  monotx_restored_types:                  0
% 3.57/0.98  sat_num_of_epr_types:                   0
% 3.57/0.98  sat_num_of_non_cyclic_types:            0
% 3.57/0.98  sat_guarded_non_collapsed_types:        0
% 3.57/0.98  num_pure_diseq_elim:                    0
% 3.57/0.98  simp_replaced_by:                       0
% 3.57/0.98  res_preprocessed:                       61
% 3.57/0.98  prep_upred:                             0
% 3.57/0.98  prep_unflattend:                        52
% 3.57/0.98  smt_new_axioms:                         0
% 3.57/0.98  pred_elim_cands:                        2
% 3.57/0.98  pred_elim:                              0
% 3.57/0.98  pred_elim_cl:                           0
% 3.57/0.98  pred_elim_cycles:                       2
% 3.57/0.98  merged_defs:                            6
% 3.57/0.98  merged_defs_ncl:                        0
% 3.57/0.98  bin_hyper_res:                          6
% 3.57/0.98  prep_cycles:                            3
% 3.57/0.98  pred_elim_time:                         0.01
% 3.57/0.98  splitting_time:                         0.
% 3.57/0.98  sem_filter_time:                        0.
% 3.57/0.98  monotx_time:                            0.
% 3.57/0.98  subtype_inf_time:                       0.
% 3.57/0.98  
% 3.57/0.98  ------ Problem properties
% 3.57/0.98  
% 3.57/0.98  clauses:                                16
% 3.57/0.98  conjectures:                            1
% 3.57/0.98  epr:                                    0
% 3.57/0.98  horn:                                   12
% 3.57/0.98  ground:                                 1
% 3.57/0.98  unary:                                  7
% 3.57/0.98  binary:                                 2
% 3.57/0.98  lits:                                   35
% 3.57/0.98  lits_eq:                                16
% 3.57/0.98  fd_pure:                                0
% 3.57/0.98  fd_pseudo:                              0
% 3.57/0.98  fd_cond:                                0
% 3.57/0.98  fd_pseudo_cond:                         6
% 3.57/0.98  ac_symbols:                             0
% 3.57/0.98  
% 3.57/0.98  ------ Propositional Solver
% 3.57/0.98  
% 3.57/0.98  prop_solver_calls:                      24
% 3.57/0.98  prop_fast_solver_calls:                 579
% 3.57/0.98  smt_solver_calls:                       0
% 3.57/0.98  smt_fast_solver_calls:                  0
% 3.57/0.98  prop_num_of_clauses:                    1459
% 3.57/0.98  prop_preprocess_simplified:             4118
% 3.57/0.98  prop_fo_subsumed:                       0
% 3.57/0.98  prop_solver_time:                       0.
% 3.57/0.98  smt_solver_time:                        0.
% 3.57/0.98  smt_fast_solver_time:                   0.
% 3.57/0.98  prop_fast_solver_time:                  0.
% 3.57/0.98  prop_unsat_core_time:                   0.
% 3.57/0.98  
% 3.57/0.98  ------ QBF
% 3.57/0.98  
% 3.57/0.98  qbf_q_res:                              0
% 3.57/0.98  qbf_num_tautologies:                    0
% 3.57/0.98  qbf_prep_cycles:                        0
% 3.57/0.98  
% 3.57/0.98  ------ BMC1
% 3.57/0.98  
% 3.57/0.98  bmc1_current_bound:                     -1
% 3.57/0.98  bmc1_last_solved_bound:                 -1
% 3.57/0.98  bmc1_unsat_core_size:                   -1
% 3.57/0.98  bmc1_unsat_core_parents_size:           -1
% 3.57/0.98  bmc1_merge_next_fun:                    0
% 3.57/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation
% 3.57/0.98  
% 3.57/0.98  inst_num_of_clauses:                    369
% 3.57/0.98  inst_num_in_passive:                    206
% 3.57/0.98  inst_num_in_active:                     151
% 3.57/0.98  inst_num_in_unprocessed:                11
% 3.57/0.98  inst_num_of_loops:                      210
% 3.57/0.98  inst_num_of_learning_restarts:          0
% 3.57/0.98  inst_num_moves_active_passive:          55
% 3.57/0.98  inst_lit_activity:                      0
% 3.57/0.98  inst_lit_activity_moves:                0
% 3.57/0.98  inst_num_tautologies:                   0
% 3.57/0.98  inst_num_prop_implied:                  0
% 3.57/0.98  inst_num_existing_simplified:           0
% 3.57/0.98  inst_num_eq_res_simplified:             0
% 3.57/0.98  inst_num_child_elim:                    0
% 3.57/0.98  inst_num_of_dismatching_blockings:      217
% 3.57/0.98  inst_num_of_non_proper_insts:           490
% 3.57/0.98  inst_num_of_duplicates:                 0
% 3.57/0.98  inst_inst_num_from_inst_to_res:         0
% 3.57/0.98  inst_dismatching_checking_time:         0.
% 3.57/0.98  
% 3.57/0.98  ------ Resolution
% 3.57/0.98  
% 3.57/0.98  res_num_of_clauses:                     0
% 3.57/0.98  res_num_in_passive:                     0
% 3.57/0.98  res_num_in_active:                      0
% 3.57/0.98  res_num_of_loops:                       64
% 3.57/0.98  res_forward_subset_subsumed:            33
% 3.57/0.98  res_backward_subset_subsumed:           0
% 3.57/0.98  res_forward_subsumed:                   0
% 3.57/0.98  res_backward_subsumed:                  0
% 3.57/0.98  res_forward_subsumption_resolution:     0
% 3.57/0.98  res_backward_subsumption_resolution:    0
% 3.57/0.98  res_clause_to_clause_subsumption:       1278
% 3.57/0.98  res_orphan_elimination:                 0
% 3.57/0.98  res_tautology_del:                      69
% 3.57/0.98  res_num_eq_res_simplified:              0
% 3.57/0.98  res_num_sel_changes:                    0
% 3.57/0.98  res_moves_from_active_to_pass:          0
% 3.57/0.98  
% 3.57/0.98  ------ Superposition
% 3.57/0.98  
% 3.57/0.98  sup_time_total:                         0.
% 3.57/0.98  sup_time_generating:                    0.
% 3.57/0.98  sup_time_sim_full:                      0.
% 3.57/0.98  sup_time_sim_immed:                     0.
% 3.57/0.98  
% 3.57/0.98  sup_num_of_clauses:                     166
% 3.57/0.98  sup_num_in_active:                      40
% 3.57/0.98  sup_num_in_passive:                     126
% 3.57/0.98  sup_num_of_loops:                       40
% 3.57/0.98  sup_fw_superposition:                   109
% 3.57/0.98  sup_bw_superposition:                   83
% 3.57/0.98  sup_immediate_simplified:               20
% 3.57/0.98  sup_given_eliminated:                   0
% 3.57/0.98  comparisons_done:                       0
% 3.57/0.98  comparisons_avoided:                    23
% 3.57/0.98  
% 3.57/0.98  ------ Simplifications
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  sim_fw_subset_subsumed:                 3
% 3.57/0.98  sim_bw_subset_subsumed:                 0
% 3.57/0.98  sim_fw_subsumed:                        16
% 3.57/0.98  sim_bw_subsumed:                        1
% 3.57/0.98  sim_fw_subsumption_res:                 0
% 3.57/0.98  sim_bw_subsumption_res:                 0
% 3.57/0.98  sim_tautology_del:                      2
% 3.57/0.98  sim_eq_tautology_del:                   7
% 3.57/0.98  sim_eq_res_simp:                        0
% 3.57/0.98  sim_fw_demodulated:                     0
% 3.57/0.98  sim_bw_demodulated:                     0
% 3.57/0.98  sim_light_normalised:                   0
% 3.57/0.98  sim_joinable_taut:                      0
% 3.57/0.98  sim_joinable_simp:                      0
% 3.57/0.98  sim_ac_normalised:                      0
% 3.57/0.98  sim_smt_subsumption:                    0
% 3.57/0.98  
%------------------------------------------------------------------------------
