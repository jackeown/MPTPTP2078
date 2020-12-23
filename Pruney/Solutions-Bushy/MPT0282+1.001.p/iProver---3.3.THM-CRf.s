%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0282+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:55 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 299 expanded)
%              Number of clauses        :   33 (  77 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  237 (1488 expanded)
%              Number of equality atoms :   40 ( 261 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) != k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,
    ( ? [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) != k1_zfmisc_1(k3_xboole_0(X0,X1))
   => k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) != k1_zfmisc_1(k3_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) != k1_zfmisc_1(k3_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f23])).

fof(f39,plain,(
    k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) != k1_zfmisc_1(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1284,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(X0))
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3323,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) != k1_zfmisc_1(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2169,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3)))
    | r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2643,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3))
    | r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_2169,c_4])).

cnf(c_711,plain,
    ( ~ r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3))
    | r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_724,plain,
    ( ~ r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2))
    | r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2371,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3)))
    | r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_14])).

cnf(c_2652,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2))
    | r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_2371,c_4])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2688,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK3)
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2810,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2643,c_711,c_724,c_2652,c_2688])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_187,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1248,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_191,c_187])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1712,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_1248,c_0])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1729,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_1712,c_11])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1749,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_1729,c_13])).

cnf(c_2828,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_2810,c_1749])).

cnf(c_1126,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_2826,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_2810,c_1126])).

cnf(c_1290,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2))
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_1169,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3)))
    | ~ r1_tarski(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_809,plain,
    ( ~ r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3),k1_zfmisc_1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2))
    | k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3323,c_2828,c_2826,c_2810,c_1290,c_1169,c_809,c_14])).


%------------------------------------------------------------------------------
