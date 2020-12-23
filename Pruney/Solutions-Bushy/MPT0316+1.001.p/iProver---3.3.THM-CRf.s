%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0316+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:59 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 154 expanded)
%              Number of clauses        :   27 (  44 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 657 expanded)
%              Number of equality atoms :   67 ( 227 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK2,sK4)
        | sK1 != sK3
        | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) )
      & ( ( r2_hidden(sK2,sK4)
          & sK1 = sK3 )
        | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ r2_hidden(sK2,sK4)
      | sK1 != sK3
      | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) )
    & ( ( r2_hidden(sK2,sK4)
        & sK1 = sK3 )
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).

fof(f25,plain,
    ( ~ r2_hidden(sK2,sK4)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(rectify,[],[f6])).

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f17])).

fof(f27,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK2),k2_zfmisc_1(X1,sK4))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_429,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(k4_tarski(X0,sK2),k2_zfmisc_1(k1_tarski(X0),sK4))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_431,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),sK4))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))
    | ~ r2_hidden(sK2,sK4)
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_292,plain,
    ( sK1 != sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_294,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_291,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_322,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_294,c_291])).

cnf(c_340,plain,
    ( sK3 != sK1
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_292,c_322])).

cnf(c_12,plain,
    ( sK1 != sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))
    | sK1 = sK3 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_290,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_370,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_376,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))
    | r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_382,plain,
    ( sK1 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_9,c_370,c_376])).

cnf(c_418,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_9,c_12,c_322,c_370,c_376])).

cnf(c_422,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_418,c_382])).

cnf(c_424,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_422])).

cnf(c_357,plain,
    ( r2_hidden(sK2,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_322])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_24,plain,
    ( r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_431,c_424,c_357,c_24])).


%------------------------------------------------------------------------------
