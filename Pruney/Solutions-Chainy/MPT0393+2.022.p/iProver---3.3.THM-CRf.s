%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 557 expanded)
%              Number of clauses        :   70 ( 118 expanded)
%              Number of leaves         :   21 ( 140 expanded)
%              Depth                    :   22
%              Number of atoms          :  473 (1774 expanded)
%              Number of equality atoms :  256 ( 965 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f99,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f92,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f40])).

fof(f69,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f90,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f91,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f90])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f95,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f96,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f95])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f38])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1045,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1041,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1038,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1055,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1054,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2322,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1054])).

cnf(c_3955,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1054])).

cnf(c_6103,plain,
    ( r2_hidden(sK0(X0,X1),k2_enumset1(X2,X2,X2,X2)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_3955])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1056,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6353,plain,
    ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6103,c_1056])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1040,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6608,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6353,c_1040])).

cnf(c_7084,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_6608])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1048,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7092,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7084,c_1048])).

cnf(c_7471,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK2(X0,X1,k1_xboole_0) = X1
    | sK2(X0,X1,k1_xboole_0) = X0
    | sK2(X0,X1,k1_xboole_0) = X2 ),
    inference(superposition,[status(thm)],[c_1045,c_7092])).

cnf(c_24,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_22069,plain,
    ( sK2(sK4,sK4,k1_xboole_0) = X0
    | sK2(sK4,sK4,k1_xboole_0) = sK4
    | k1_setfam_1(k1_xboole_0) != sK4 ),
    inference(superposition,[status(thm)],[c_7471,c_24])).

cnf(c_511,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_510,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2368,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_511,c_510])).

cnf(c_1531,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

cnf(c_1783,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_1531,c_9])).

cnf(c_2375,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2368,c_1783])).

cnf(c_2512,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2375,c_24])).

cnf(c_2513,plain,
    ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2512])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22021,plain,
    ( sK2(X0,X0,k1_xboole_0) = X0
    | sK2(X0,X0,k1_xboole_0) = X1
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7471,c_1049])).

cnf(c_22253,plain,
    ( sK2(sK4,sK4,k1_xboole_0) = sK4
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22021])).

cnf(c_22618,plain,
    ( sK2(sK4,sK4,k1_xboole_0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22069,c_2513,c_22253])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1047,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) != X1
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22624,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK2(sK4,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22618,c_1047])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_50,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_53,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_72,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_514,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_518,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1111,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1124,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1126,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1345,plain,
    ( X0 != X1
    | k2_enumset1(sK4,sK4,sK4,sK4) != X1
    | k2_enumset1(sK4,sK4,sK4,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_2162,plain,
    ( X0 != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = X0
    | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_3718,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3719,plain,
    ( ~ r1_tarski(X0,sK3(k2_enumset1(sK4,sK4,sK4,sK4),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3721,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3719])).

cnf(c_22,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2103,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_22,c_9])).

cnf(c_512,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9876,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_2103,c_512])).

cnf(c_9890,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r1_tarski(sK4,sK4)
    | sK4 != sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9876])).

cnf(c_23261,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22624,c_24,c_50,c_53,c_72,c_518,c_1111,c_1126,c_3718,c_3721,c_9890])).

cnf(c_1043,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_23341,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23261,c_1043])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23341,c_2513])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 7.87/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/1.51  
% 7.87/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.51  
% 7.87/1.51  ------  iProver source info
% 7.87/1.51  
% 7.87/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.51  git: non_committed_changes: false
% 7.87/1.51  git: last_make_outside_of_git: false
% 7.87/1.51  
% 7.87/1.51  ------ 
% 7.87/1.51  ------ Parsing...
% 7.87/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.51  
% 7.87/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.87/1.51  
% 7.87/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.51  
% 7.87/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.51  ------ Proving...
% 7.87/1.51  ------ Problem Properties 
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  clauses                                 24
% 7.87/1.51  conjectures                             1
% 7.87/1.51  EPR                                     3
% 7.87/1.51  Horn                                    17
% 7.87/1.51  unary                                   7
% 7.87/1.51  binary                                  5
% 7.87/1.51  lits                                    54
% 7.87/1.51  lits eq                                 20
% 7.87/1.51  fd_pure                                 0
% 7.87/1.51  fd_pseudo                               0
% 7.87/1.51  fd_cond                                 2
% 7.87/1.51  fd_pseudo_cond                          7
% 7.87/1.51  AC symbols                              0
% 7.87/1.51  
% 7.87/1.51  ------ Input Options Time Limit: Unbounded
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  ------ 
% 7.87/1.51  Current options:
% 7.87/1.51  ------ 
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  ------ Proving...
% 7.87/1.51  
% 7.87/1.51  
% 7.87/1.51  % SZS status Theorem for theBenchmark.p
% 7.87/1.51  
% 7.87/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.51  
% 7.87/1.51  fof(f4,axiom,(
% 7.87/1.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f30,plain,(
% 7.87/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.87/1.51    inference(nnf_transformation,[],[f4])).
% 7.87/1.51  
% 7.87/1.51  fof(f31,plain,(
% 7.87/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.87/1.51    inference(flattening,[],[f30])).
% 7.87/1.51  
% 7.87/1.51  fof(f32,plain,(
% 7.87/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.87/1.51    inference(rectify,[],[f31])).
% 7.87/1.51  
% 7.87/1.51  fof(f33,plain,(
% 7.87/1.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.87/1.51    introduced(choice_axiom,[])).
% 7.87/1.51  
% 7.87/1.51  fof(f34,plain,(
% 7.87/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.87/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 7.87/1.51  
% 7.87/1.51  fof(f55,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f34])).
% 7.87/1.51  
% 7.87/1.51  fof(f6,axiom,(
% 7.87/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f59,plain,(
% 7.87/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f6])).
% 7.87/1.51  
% 7.87/1.51  fof(f7,axiom,(
% 7.87/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f60,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f7])).
% 7.87/1.51  
% 7.87/1.51  fof(f70,plain,(
% 7.87/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f59,f60])).
% 7.87/1.51  
% 7.87/1.51  fof(f78,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f55,f70])).
% 7.87/1.51  
% 7.87/1.51  fof(f8,axiom,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f35,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.87/1.51    inference(nnf_transformation,[],[f8])).
% 7.87/1.51  
% 7.87/1.51  fof(f62,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f35])).
% 7.87/1.51  
% 7.87/1.51  fof(f5,axiom,(
% 7.87/1.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f58,plain,(
% 7.87/1.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f5])).
% 7.87/1.51  
% 7.87/1.51  fof(f71,plain,(
% 7.87/1.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f58,f70])).
% 7.87/1.51  
% 7.87/1.51  fof(f82,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f62,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f9,axiom,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f36,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.87/1.51    inference(nnf_transformation,[],[f9])).
% 7.87/1.51  
% 7.87/1.51  fof(f37,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.87/1.51    inference(flattening,[],[f36])).
% 7.87/1.51  
% 7.87/1.51  fof(f64,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 7.87/1.51    inference(cnf_transformation,[],[f37])).
% 7.87/1.51  
% 7.87/1.51  fof(f85,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 7.87/1.51    inference(definition_unfolding,[],[f64,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f99,plain,(
% 7.87/1.51    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.87/1.51    inference(equality_resolution,[],[f85])).
% 7.87/1.51  
% 7.87/1.51  fof(f1,axiom,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f14,plain,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.87/1.51    inference(ennf_transformation,[],[f1])).
% 7.87/1.51  
% 7.87/1.51  fof(f20,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.51    inference(nnf_transformation,[],[f14])).
% 7.87/1.51  
% 7.87/1.51  fof(f21,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.51    inference(rectify,[],[f20])).
% 7.87/1.51  
% 7.87/1.51  fof(f22,plain,(
% 7.87/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.87/1.51    introduced(choice_axiom,[])).
% 7.87/1.51  
% 7.87/1.51  fof(f23,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 7.87/1.51  
% 7.87/1.51  fof(f43,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f23])).
% 7.87/1.51  
% 7.87/1.51  fof(f42,plain,(
% 7.87/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f23])).
% 7.87/1.51  
% 7.87/1.51  fof(f44,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f23])).
% 7.87/1.51  
% 7.87/1.51  fof(f61,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f35])).
% 7.87/1.51  
% 7.87/1.51  fof(f83,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f61,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f3,axiom,(
% 7.87/1.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f26,plain,(
% 7.87/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.87/1.51    inference(nnf_transformation,[],[f3])).
% 7.87/1.51  
% 7.87/1.51  fof(f27,plain,(
% 7.87/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.87/1.51    inference(rectify,[],[f26])).
% 7.87/1.51  
% 7.87/1.51  fof(f28,plain,(
% 7.87/1.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.87/1.51    introduced(choice_axiom,[])).
% 7.87/1.51  
% 7.87/1.51  fof(f29,plain,(
% 7.87/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.87/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.87/1.51  
% 7.87/1.51  fof(f48,plain,(
% 7.87/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.87/1.51    inference(cnf_transformation,[],[f29])).
% 7.87/1.51  
% 7.87/1.51  fof(f75,plain,(
% 7.87/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.87/1.51    inference(definition_unfolding,[],[f48,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f92,plain,(
% 7.87/1.51    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.87/1.51    inference(equality_resolution,[],[f75])).
% 7.87/1.51  
% 7.87/1.51  fof(f12,conjecture,(
% 7.87/1.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f13,negated_conjecture,(
% 7.87/1.51    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.87/1.51    inference(negated_conjecture,[],[f12])).
% 7.87/1.51  
% 7.87/1.51  fof(f19,plain,(
% 7.87/1.51    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.87/1.51    inference(ennf_transformation,[],[f13])).
% 7.87/1.51  
% 7.87/1.51  fof(f40,plain,(
% 7.87/1.51    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.87/1.51    introduced(choice_axiom,[])).
% 7.87/1.51  
% 7.87/1.51  fof(f41,plain,(
% 7.87/1.51    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.87/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f40])).
% 7.87/1.51  
% 7.87/1.51  fof(f69,plain,(
% 7.87/1.51    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.87/1.51    inference(cnf_transformation,[],[f41])).
% 7.87/1.51  
% 7.87/1.51  fof(f87,plain,(
% 7.87/1.51    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 7.87/1.51    inference(definition_unfolding,[],[f69,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f49,plain,(
% 7.87/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.87/1.51    inference(cnf_transformation,[],[f29])).
% 7.87/1.51  
% 7.87/1.51  fof(f74,plain,(
% 7.87/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.87/1.51    inference(definition_unfolding,[],[f49,f71])).
% 7.87/1.51  
% 7.87/1.51  fof(f90,plain,(
% 7.87/1.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.87/1.51    inference(equality_resolution,[],[f74])).
% 7.87/1.51  
% 7.87/1.51  fof(f91,plain,(
% 7.87/1.51    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.87/1.51    inference(equality_resolution,[],[f90])).
% 7.87/1.51  
% 7.87/1.51  fof(f57,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f34])).
% 7.87/1.51  
% 7.87/1.51  fof(f76,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.87/1.51    inference(definition_unfolding,[],[f57,f70])).
% 7.87/1.51  
% 7.87/1.51  fof(f52,plain,(
% 7.87/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.87/1.51    inference(cnf_transformation,[],[f34])).
% 7.87/1.51  
% 7.87/1.51  fof(f81,plain,(
% 7.87/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.87/1.51    inference(definition_unfolding,[],[f52,f70])).
% 7.87/1.51  
% 7.87/1.51  fof(f97,plain,(
% 7.87/1.51    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.87/1.51    inference(equality_resolution,[],[f81])).
% 7.87/1.51  
% 7.87/1.51  fof(f53,plain,(
% 7.87/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.87/1.51    inference(cnf_transformation,[],[f34])).
% 7.87/1.51  
% 7.87/1.51  fof(f80,plain,(
% 7.87/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.87/1.51    inference(definition_unfolding,[],[f53,f70])).
% 7.87/1.51  
% 7.87/1.51  fof(f95,plain,(
% 7.87/1.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.87/1.51    inference(equality_resolution,[],[f80])).
% 7.87/1.51  
% 7.87/1.51  fof(f96,plain,(
% 7.87/1.51    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.87/1.51    inference(equality_resolution,[],[f95])).
% 7.87/1.51  
% 7.87/1.51  fof(f2,axiom,(
% 7.87/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f24,plain,(
% 7.87/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.51    inference(nnf_transformation,[],[f2])).
% 7.87/1.51  
% 7.87/1.51  fof(f25,plain,(
% 7.87/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.51    inference(flattening,[],[f24])).
% 7.87/1.51  
% 7.87/1.51  fof(f45,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.87/1.51    inference(cnf_transformation,[],[f25])).
% 7.87/1.51  
% 7.87/1.51  fof(f89,plain,(
% 7.87/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.87/1.51    inference(equality_resolution,[],[f45])).
% 7.87/1.51  
% 7.87/1.51  fof(f47,plain,(
% 7.87/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f25])).
% 7.87/1.51  
% 7.87/1.51  fof(f11,axiom,(
% 7.87/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f17,plain,(
% 7.87/1.51    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 7.87/1.51    inference(ennf_transformation,[],[f11])).
% 7.87/1.51  
% 7.87/1.51  fof(f18,plain,(
% 7.87/1.51    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 7.87/1.51    inference(flattening,[],[f17])).
% 7.87/1.51  
% 7.87/1.51  fof(f68,plain,(
% 7.87/1.51    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.87/1.51    inference(cnf_transformation,[],[f18])).
% 7.87/1.51  
% 7.87/1.51  fof(f10,axiom,(
% 7.87/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 7.87/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.51  
% 7.87/1.51  fof(f15,plain,(
% 7.87/1.51    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.87/1.51    inference(ennf_transformation,[],[f10])).
% 7.87/1.51  
% 7.87/1.51  fof(f16,plain,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.87/1.51    inference(flattening,[],[f15])).
% 7.87/1.51  
% 7.87/1.51  fof(f38,plain,(
% 7.87/1.51    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 7.87/1.51    introduced(choice_axiom,[])).
% 7.87/1.51  
% 7.87/1.51  fof(f39,plain,(
% 7.87/1.51    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 7.87/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f38])).
% 7.87/1.51  
% 7.87/1.51  fof(f67,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 7.87/1.51    inference(cnf_transformation,[],[f39])).
% 7.87/1.51  
% 7.87/1.51  fof(f66,plain,(
% 7.87/1.51    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 7.87/1.52    inference(cnf_transformation,[],[f39])).
% 7.87/1.52  
% 7.87/1.52  cnf(c_12,plain,
% 7.87/1.52      ( r2_hidden(sK2(X0,X1,X2),X2)
% 7.87/1.52      | k2_enumset1(X0,X0,X0,X1) = X2
% 7.87/1.52      | sK2(X0,X1,X2) = X1
% 7.87/1.52      | sK2(X0,X1,X2) = X0 ),
% 7.87/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1045,plain,
% 7.87/1.52      ( k2_enumset1(X0,X0,X0,X1) = X2
% 7.87/1.52      | sK2(X0,X1,X2) = X1
% 7.87/1.52      | sK2(X0,X1,X2) = X0
% 7.87/1.52      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_16,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 7.87/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1041,plain,
% 7.87/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.87/1.52      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_19,plain,
% 7.87/1.52      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.87/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1038,plain,
% 7.87/1.52      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.87/1.52      inference(cnf_transformation,[],[f43]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1055,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.87/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.87/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1054,plain,
% 7.87/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.87/1.52      | r2_hidden(X0,X2) = iProver_top
% 7.87/1.52      | r1_tarski(X1,X2) != iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2322,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.87/1.52      | r1_tarski(X0,X2) != iProver_top
% 7.87/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_1055,c_1054]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_3955,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.87/1.52      | r1_tarski(X0,X3) != iProver_top
% 7.87/1.52      | r1_tarski(X3,X2) != iProver_top
% 7.87/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_2322,c_1054]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_6103,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),k2_enumset1(X2,X2,X2,X2)) = iProver_top
% 7.87/1.52      | r1_tarski(X0,X1) = iProver_top
% 7.87/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_1038,c_3955]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_0,plain,
% 7.87/1.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.87/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1056,plain,
% 7.87/1.52      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.87/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_6353,plain,
% 7.87/1.52      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
% 7.87/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_6103,c_1056]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_17,plain,
% 7.87/1.52      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 7.87/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1040,plain,
% 7.87/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.87/1.52      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_6608,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
% 7.87/1.52      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_6353,c_1040]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_7084,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top
% 7.87/1.52      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_1041,c_6608]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_9,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.87/1.52      inference(cnf_transformation,[],[f92]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1048,plain,
% 7.87/1.52      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_7092,plain,
% 7.87/1.52      ( X0 = X1 | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_7084,c_1048]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_7471,plain,
% 7.87/1.52      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 7.87/1.52      | sK2(X0,X1,k1_xboole_0) = X1
% 7.87/1.52      | sK2(X0,X1,k1_xboole_0) = X0
% 7.87/1.52      | sK2(X0,X1,k1_xboole_0) = X2 ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_1045,c_7092]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_24,negated_conjecture,
% 7.87/1.52      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 7.87/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22069,plain,
% 7.87/1.52      ( sK2(sK4,sK4,k1_xboole_0) = X0
% 7.87/1.52      | sK2(sK4,sK4,k1_xboole_0) = sK4
% 7.87/1.52      | k1_setfam_1(k1_xboole_0) != sK4 ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_7471,c_24]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_511,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_510,plain,( X0 = X0 ),theory(equality) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2368,plain,
% 7.87/1.52      ( X0 != X1 | X1 = X0 ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_511,c_510]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1531,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
% 7.87/1.52      | ~ r2_hidden(X0,k1_xboole_0) ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_2,c_19]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1783,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,k1_xboole_0) | X0 = X1 ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_1531,c_9]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2375,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,k1_xboole_0) | X1 = X0 ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_2368,c_1783]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2512,plain,
% 7.87/1.52      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_2375,c_24]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2513,plain,
% 7.87/1.52      ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_2512]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_8,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.87/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1049,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22021,plain,
% 7.87/1.52      ( sK2(X0,X0,k1_xboole_0) = X0
% 7.87/1.52      | sK2(X0,X0,k1_xboole_0) = X1
% 7.87/1.52      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_7471,c_1049]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22253,plain,
% 7.87/1.52      ( sK2(sK4,sK4,k1_xboole_0) = sK4
% 7.87/1.52      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_22021]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22618,plain,
% 7.87/1.52      ( sK2(sK4,sK4,k1_xboole_0) = sK4 ),
% 7.87/1.52      inference(global_propositional_subsumption,
% 7.87/1.52                [status(thm)],
% 7.87/1.52                [c_22069,c_2513,c_22253]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_10,plain,
% 7.87/1.52      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
% 7.87/1.52      | k2_enumset1(X0,X0,X0,X1) = X2
% 7.87/1.52      | sK2(X0,X1,X2) != X1 ),
% 7.87/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1047,plain,
% 7.87/1.52      ( k2_enumset1(X0,X0,X0,X1) = X2
% 7.87/1.52      | sK2(X0,X1,X2) != X1
% 7.87/1.52      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22624,plain,
% 7.87/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.87/1.52      | r2_hidden(sK2(sK4,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_22618,c_1047]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_15,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.87/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_50,plain,
% 7.87/1.52      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_15]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_14,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.87/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_53,plain,
% 7.87/1.52      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_14]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_5,plain,
% 7.87/1.52      ( r1_tarski(X0,X0) ),
% 7.87/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_72,plain,
% 7.87/1.52      ( r1_tarski(sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_514,plain,
% 7.87/1.52      ( X0 != X1
% 7.87/1.52      | X2 != X3
% 7.87/1.52      | X4 != X5
% 7.87/1.52      | X6 != X7
% 7.87/1.52      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 7.87/1.52      theory(equality) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_518,plain,
% 7.87/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.87/1.52      | sK4 != sK4 ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_514]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_3,plain,
% 7.87/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.87/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1111,plain,
% 7.87/1.52      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 7.87/1.52      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.87/1.52      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_23,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,X1)
% 7.87/1.52      | ~ r1_tarski(X0,X2)
% 7.87/1.52      | r1_tarski(k1_setfam_1(X1),X2) ),
% 7.87/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1124,plain,
% 7.87/1.52      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 7.87/1.52      | ~ r1_tarski(X0,X1)
% 7.87/1.52      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_23]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1126,plain,
% 7.87/1.52      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.87/1.52      | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 7.87/1.52      | ~ r1_tarski(sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_1124]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1345,plain,
% 7.87/1.52      ( X0 != X1
% 7.87/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) != X1
% 7.87/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) = X0 ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_511]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2162,plain,
% 7.87/1.52      ( X0 != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.87/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) = X0
% 7.87/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_1345]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_3718,plain,
% 7.87/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.87/1.52      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.87/1.52      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_2162]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_21,plain,
% 7.87/1.52      ( ~ r1_tarski(X0,sK3(X1,X0))
% 7.87/1.52      | r1_tarski(X0,k1_setfam_1(X1))
% 7.87/1.52      | k1_xboole_0 = X1 ),
% 7.87/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_3719,plain,
% 7.87/1.52      ( ~ r1_tarski(X0,sK3(k2_enumset1(sK4,sK4,sK4,sK4),X0))
% 7.87/1.52      | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.87/1.52      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_21]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_3721,plain,
% 7.87/1.52      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.87/1.52      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.87/1.52      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_3719]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_22,plain,
% 7.87/1.52      ( r2_hidden(sK3(X0,X1),X0)
% 7.87/1.52      | r1_tarski(X1,k1_setfam_1(X0))
% 7.87/1.52      | k1_xboole_0 = X0 ),
% 7.87/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_2103,plain,
% 7.87/1.52      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 7.87/1.52      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 7.87/1.52      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_22,c_9]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_512,plain,
% 7.87/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.87/1.52      theory(equality) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_9876,plain,
% 7.87/1.52      ( ~ r1_tarski(X0,X1)
% 7.87/1.52      | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X3))
% 7.87/1.52      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 7.87/1.52      | X2 != X0
% 7.87/1.52      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 7.87/1.52      inference(resolution,[status(thm)],[c_2103,c_512]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_9890,plain,
% 7.87/1.52      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.87/1.52      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 7.87/1.52      | ~ r1_tarski(sK4,sK4)
% 7.87/1.52      | sK4 != sK4
% 7.87/1.52      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.87/1.52      inference(instantiation,[status(thm)],[c_9876]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_23261,plain,
% 7.87/1.52      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 7.87/1.52      inference(global_propositional_subsumption,
% 7.87/1.52                [status(thm)],
% 7.87/1.52                [c_22624,c_24,c_50,c_53,c_72,c_518,c_1111,c_1126,c_3718,
% 7.87/1.52                 c_3721,c_9890]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_1043,plain,
% 7.87/1.52      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 7.87/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(c_23341,plain,
% 7.87/1.52      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.87/1.52      inference(superposition,[status(thm)],[c_23261,c_1043]) ).
% 7.87/1.52  
% 7.87/1.52  cnf(contradiction,plain,
% 7.87/1.52      ( $false ),
% 7.87/1.52      inference(minisat,[status(thm)],[c_23341,c_2513]) ).
% 7.87/1.52  
% 7.87/1.52  
% 7.87/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.52  
% 7.87/1.52  ------                               Statistics
% 7.87/1.52  
% 7.87/1.52  ------ Selected
% 7.87/1.52  
% 7.87/1.52  total_time:                             0.802
% 7.87/1.52  
%------------------------------------------------------------------------------
