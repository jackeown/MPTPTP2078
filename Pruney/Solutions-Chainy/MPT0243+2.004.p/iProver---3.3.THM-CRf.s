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
% DateTime   : Thu Dec  3 11:31:54 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 121 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  275 ( 658 expanded)
%              Number of equality atoms :  108 ( 271 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f90,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f88,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f87])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r2_hidden(sK3,sK5)
        | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
      & ( ( r2_hidden(sK4,sK5)
          & r2_hidden(sK3,sK5) )
        | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r2_hidden(sK3,sK5)
      | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
    & ( ( r2_hidden(sK4,sK5)
        & r2_hidden(sK3,sK5) )
      | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f42,f43])).

fof(f74,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f74,f69])).

fof(f76,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f76,f69])).

fof(f75,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f75,f69])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16600,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_16659,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_16600])).

cnf(c_16660,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_16659])).

cnf(c_17007,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | ~ r2_hidden(sK4,sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK4 ),
    inference(instantiation,[status(thm)],[c_16660])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_16700,plain,
    ( ~ r2_hidden(sK0(X0,sK5),k1_enumset1(X1,X2,X3))
    | sK0(X0,sK5) = X1
    | sK0(X0,sK5) = X2
    | sK0(X0,sK5) = X3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_16749,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4))
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK3
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_16700])).

cnf(c_16662,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | ~ r2_hidden(sK3,sK5)
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_16660])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16569,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16570,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4))
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3247,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3242,plain,
    ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3160,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_enumset1(X2,X3,X0))
    | ~ r1_tarski(k1_enumset1(X2,X3,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3230,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4))
    | r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_3160])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3219,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK4))
    | r2_hidden(X0,sK5)
    | r2_hidden(sK3,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

cnf(c_3221,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK4))
    | r2_hidden(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_3219])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17007,c_16749,c_16662,c_16569,c_16570,c_3247,c_3242,c_3230,c_3221,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n012.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:50:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 3.82/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.97  
% 3.82/0.97  ------  iProver source info
% 3.82/0.97  
% 3.82/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.97  git: non_committed_changes: false
% 3.82/0.97  git: last_make_outside_of_git: false
% 3.82/0.97  
% 3.82/0.97  ------ 
% 3.82/0.97  ------ Parsing...
% 3.82/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  ------ Proving...
% 3.82/0.97  ------ Problem Properties 
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  clauses                                 30
% 3.82/0.97  conjectures                             3
% 3.82/0.97  EPR                                     4
% 3.82/0.97  Horn                                    22
% 3.82/0.97  unary                                   5
% 3.82/0.97  binary                                  11
% 3.82/0.97  lits                                    73
% 3.82/0.97  lits eq                                 21
% 3.82/0.97  fd_pure                                 0
% 3.82/0.97  fd_pseudo                               0
% 3.82/0.97  fd_cond                                 0
% 3.82/0.97  fd_pseudo_cond                          9
% 3.82/0.97  AC symbols                              0
% 3.82/0.97  
% 3.82/0.97  ------ Input Options Time Limit: Unbounded
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing...
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.82/0.97  Current options:
% 3.82/0.97  ------ 
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  % SZS status Theorem for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  fof(f8,axiom,(
% 3.82/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f21,plain,(
% 3.82/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.82/0.97    inference(ennf_transformation,[],[f8])).
% 3.82/0.97  
% 3.82/0.97  fof(f35,plain,(
% 3.82/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.82/0.97    inference(nnf_transformation,[],[f21])).
% 3.82/0.97  
% 3.82/0.97  fof(f36,plain,(
% 3.82/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.82/0.97    inference(flattening,[],[f35])).
% 3.82/0.97  
% 3.82/0.97  fof(f37,plain,(
% 3.82/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.82/0.97    inference(rectify,[],[f36])).
% 3.82/0.97  
% 3.82/0.97  fof(f38,plain,(
% 3.82/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.82/0.97    introduced(choice_axiom,[])).
% 3.82/0.97  
% 3.82/0.97  fof(f39,plain,(
% 3.82/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 3.82/0.97  
% 3.82/0.97  fof(f61,plain,(
% 3.82/0.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.82/0.97    inference(cnf_transformation,[],[f39])).
% 3.82/0.97  
% 3.82/0.97  fof(f93,plain,(
% 3.82/0.97    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 3.82/0.97    inference(equality_resolution,[],[f61])).
% 3.82/0.97  
% 3.82/0.97  fof(f1,axiom,(
% 3.82/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f15,plain,(
% 3.82/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.82/0.97    inference(ennf_transformation,[],[f1])).
% 3.82/0.97  
% 3.82/0.97  fof(f24,plain,(
% 3.82/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.97    inference(nnf_transformation,[],[f15])).
% 3.82/0.97  
% 3.82/0.97  fof(f25,plain,(
% 3.82/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.97    inference(rectify,[],[f24])).
% 3.82/0.97  
% 3.82/0.97  fof(f26,plain,(
% 3.82/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.82/0.97    introduced(choice_axiom,[])).
% 3.82/0.97  
% 3.82/0.97  fof(f27,plain,(
% 3.82/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.82/0.97  
% 3.82/0.97  fof(f47,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f27])).
% 3.82/0.97  
% 3.82/0.97  fof(f46,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f27])).
% 3.82/0.97  
% 3.82/0.97  fof(f63,plain,(
% 3.82/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.82/0.97    inference(cnf_transformation,[],[f39])).
% 3.82/0.97  
% 3.82/0.97  fof(f89,plain,(
% 3.82/0.97    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 3.82/0.97    inference(equality_resolution,[],[f63])).
% 3.82/0.97  
% 3.82/0.97  fof(f90,plain,(
% 3.82/0.97    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 3.82/0.97    inference(equality_resolution,[],[f89])).
% 3.82/0.97  
% 3.82/0.97  fof(f64,plain,(
% 3.82/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.82/0.97    inference(cnf_transformation,[],[f39])).
% 3.82/0.97  
% 3.82/0.97  fof(f87,plain,(
% 3.82/0.97    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.82/0.97    inference(equality_resolution,[],[f64])).
% 3.82/0.97  
% 3.82/0.97  fof(f88,plain,(
% 3.82/0.97    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.82/0.97    inference(equality_resolution,[],[f87])).
% 3.82/0.97  
% 3.82/0.97  fof(f45,plain,(
% 3.82/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f27])).
% 3.82/0.97  
% 3.82/0.97  fof(f13,conjecture,(
% 3.82/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f14,negated_conjecture,(
% 3.82/0.97    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.82/0.97    inference(negated_conjecture,[],[f13])).
% 3.82/0.97  
% 3.82/0.97  fof(f23,plain,(
% 3.82/0.97    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.82/0.97    inference(ennf_transformation,[],[f14])).
% 3.82/0.97  
% 3.82/0.97  fof(f41,plain,(
% 3.82/0.97    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.82/0.97    inference(nnf_transformation,[],[f23])).
% 3.82/0.97  
% 3.82/0.97  fof(f42,plain,(
% 3.82/0.97    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.82/0.97    inference(flattening,[],[f41])).
% 3.82/0.97  
% 3.82/0.97  fof(f43,plain,(
% 3.82/0.97    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5)))),
% 3.82/0.97    introduced(choice_axiom,[])).
% 3.82/0.97  
% 3.82/0.97  fof(f44,plain,(
% 3.82/0.97    (~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5))),
% 3.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f42,f43])).
% 3.82/0.97  
% 3.82/0.97  fof(f74,plain,(
% 3.82/0.97    r2_hidden(sK3,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.82/0.97    inference(cnf_transformation,[],[f44])).
% 3.82/0.97  
% 3.82/0.97  fof(f9,axiom,(
% 3.82/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f69,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f9])).
% 3.82/0.97  
% 3.82/0.97  fof(f81,plain,(
% 3.82/0.97    r2_hidden(sK3,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.82/0.97    inference(definition_unfolding,[],[f74,f69])).
% 3.82/0.97  
% 3.82/0.97  fof(f76,plain,(
% 3.82/0.97    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.82/0.97    inference(cnf_transformation,[],[f44])).
% 3.82/0.97  
% 3.82/0.97  fof(f79,plain,(
% 3.82/0.97    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.82/0.97    inference(definition_unfolding,[],[f76,f69])).
% 3.82/0.97  
% 3.82/0.97  fof(f75,plain,(
% 3.82/0.97    r2_hidden(sK4,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.82/0.97    inference(cnf_transformation,[],[f44])).
% 3.82/0.97  
% 3.82/0.97  fof(f80,plain,(
% 3.82/0.97    r2_hidden(sK4,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5)),
% 3.82/0.97    inference(definition_unfolding,[],[f75,f69])).
% 3.82/0.97  
% 3.82/0.97  cnf(c_524,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.82/0.97      theory(equality) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16600,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,X1)
% 3.82/0.97      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 3.82/0.97      | sK5 != X1 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_524]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16659,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,sK5)
% 3.82/0.97      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 3.82/0.97      | sK5 != sK5 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_16600]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16660,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,sK5)
% 3.82/0.97      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != X0 ),
% 3.82/0.97      inference(equality_resolution_simp,[status(thm)],[c_16659]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_17007,plain,
% 3.82/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | ~ r2_hidden(sK4,sK5)
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK4 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_16660]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_23,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 3.82/0.97      | X0 = X1
% 3.82/0.97      | X0 = X2
% 3.82/0.97      | X0 = X3 ),
% 3.82/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16700,plain,
% 3.82/0.97      ( ~ r2_hidden(sK0(X0,sK5),k1_enumset1(X1,X2,X3))
% 3.82/0.97      | sK0(X0,sK5) = X1
% 3.82/0.97      | sK0(X0,sK5) = X2
% 3.82/0.97      | sK0(X0,sK5) = X3 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_23]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16749,plain,
% 3.82/0.97      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4))
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK3
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) = sK4 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_16700]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16662,plain,
% 3.82/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | ~ r2_hidden(sK3,sK5)
% 3.82/0.97      | sK0(k1_enumset1(sK3,sK3,sK4),sK5) != sK3 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_16660]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_0,plain,
% 3.82/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.82/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16569,plain,
% 3.82/0.97      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),sK5)
% 3.82/0.97      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_1,plain,
% 3.82/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.82/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16570,plain,
% 3.82/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK4),sK5),k1_enumset1(sK3,sK3,sK4))
% 3.82/0.97      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_21,plain,
% 3.82/0.97      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
% 3.82/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3247,plain,
% 3.82/0.97      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK4)) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_21]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_20,plain,
% 3.82/0.97      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.82/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3242,plain,
% 3.82/0.97      ( r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4)) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_20]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_2,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.82/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3160,plain,
% 3.82/0.97      ( r2_hidden(X0,X1)
% 3.82/0.97      | ~ r2_hidden(X0,k1_enumset1(X2,X3,X0))
% 3.82/0.97      | ~ r1_tarski(k1_enumset1(X2,X3,X0),X1) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3230,plain,
% 3.82/0.97      ( ~ r2_hidden(sK4,k1_enumset1(sK3,sK3,sK4))
% 3.82/0.97      | r2_hidden(sK4,sK5)
% 3.82/0.97      | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_3160]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_30,negated_conjecture,
% 3.82/0.97      ( r2_hidden(sK3,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3219,plain,
% 3.82/0.97      ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK4))
% 3.82/0.97      | r2_hidden(X0,sK5)
% 3.82/0.97      | r2_hidden(sK3,sK5) ),
% 3.82/0.97      inference(resolution,[status(thm)],[c_2,c_30]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3221,plain,
% 3.82/0.97      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK4)) | r2_hidden(sK3,sK5) ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_3219]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_28,negated_conjecture,
% 3.82/0.97      ( ~ r2_hidden(sK3,sK5)
% 3.82/0.97      | ~ r2_hidden(sK4,sK5)
% 3.82/0.97      | ~ r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_29,negated_conjecture,
% 3.82/0.97      ( r2_hidden(sK4,sK5) | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 3.82/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(contradiction,plain,
% 3.82/0.97      ( $false ),
% 3.82/0.97      inference(minisat,
% 3.82/0.97                [status(thm)],
% 3.82/0.97                [c_17007,c_16749,c_16662,c_16569,c_16570,c_3247,c_3242,
% 3.82/0.97                 c_3230,c_3221,c_28,c_29]) ).
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  ------                               Statistics
% 3.82/0.97  
% 3.82/0.97  ------ Selected
% 3.82/0.97  
% 3.82/0.97  total_time:                             0.427
% 3.82/0.97  
%------------------------------------------------------------------------------
