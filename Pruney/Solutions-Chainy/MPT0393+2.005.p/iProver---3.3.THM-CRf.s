%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 19.17s
% Output     : CNFRefutation 19.17s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 190 expanded)
%              Number of clauses        :   37 (  40 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 ( 504 expanded)
%              Number of equality atoms :  114 ( 272 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f44])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f120,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f122,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f100])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f46])).

fof(f84,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f84,f86])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f78,f86])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f118,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f97])).

fof(f119,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f118])).

cnf(c_32,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1952,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_32,c_23])).

cnf(c_676,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_42282,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1952,c_676])).

cnf(c_42304,plain,
    ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_tarski(sK5,sK5)
    | sK5 != sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_42282])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2705,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

cnf(c_3219,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_2705,c_23])).

cnf(c_675,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_674,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2172,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_675,c_674])).

cnf(c_3233,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3219,c_2172])).

cnf(c_33,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3621,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3233,c_33])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2129,plain,
    ( ~ r1_tarski(X0,sK4(k2_enumset1(X1,X1,X2,X3),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
    | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2133,plain,
    ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_677,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1507,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_2070,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2074,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_27,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1360,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1528,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1360])).

cnf(c_1529,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1528])).

cnf(c_1531,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1472,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_84,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_63,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_60,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42304,c_3621,c_2133,c_2074,c_1531,c_1472,c_84,c_63,c_60,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.17/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.17/2.99  
% 19.17/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.17/2.99  
% 19.17/2.99  ------  iProver source info
% 19.17/2.99  
% 19.17/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.17/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.17/2.99  git: non_committed_changes: false
% 19.17/2.99  git: last_make_outside_of_git: false
% 19.17/2.99  
% 19.17/2.99  ------ 
% 19.17/2.99  ------ Parsing...
% 19.17/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.17/2.99  
% 19.17/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.17/2.99  
% 19.17/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.17/2.99  
% 19.17/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.17/2.99  ------ Proving...
% 19.17/2.99  ------ Problem Properties 
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  clauses                                 33
% 19.17/2.99  conjectures                             1
% 19.17/2.99  EPR                                     3
% 19.17/2.99  Horn                                    21
% 19.17/2.99  unary                                   10
% 19.17/2.99  binary                                  7
% 19.17/2.99  lits                                    76
% 19.17/2.99  lits eq                                 30
% 19.17/2.99  fd_pure                                 0
% 19.17/2.99  fd_pseudo                               0
% 19.17/2.99  fd_cond                                 2
% 19.17/2.99  fd_pseudo_cond                          11
% 19.17/2.99  AC symbols                              0
% 19.17/2.99  
% 19.17/2.99  ------ Input Options Time Limit: Unbounded
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  ------ 
% 19.17/2.99  Current options:
% 19.17/2.99  ------ 
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  ------ Proving...
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  % SZS status Theorem for theBenchmark.p
% 19.17/2.99  
% 19.17/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.17/2.99  
% 19.17/2.99  fof(f13,axiom,(
% 19.17/2.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f18,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.17/2.99    inference(ennf_transformation,[],[f13])).
% 19.17/2.99  
% 19.17/2.99  fof(f19,plain,(
% 19.17/2.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.17/2.99    inference(flattening,[],[f18])).
% 19.17/2.99  
% 19.17/2.99  fof(f44,plain,(
% 19.17/2.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 19.17/2.99    introduced(choice_axiom,[])).
% 19.17/2.99  
% 19.17/2.99  fof(f45,plain,(
% 19.17/2.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 19.17/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f44])).
% 19.17/2.99  
% 19.17/2.99  fof(f82,plain,(
% 19.17/2.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f45])).
% 19.17/2.99  
% 19.17/2.99  fof(f5,axiom,(
% 19.17/2.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f37,plain,(
% 19.17/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.17/2.99    inference(nnf_transformation,[],[f5])).
% 19.17/2.99  
% 19.17/2.99  fof(f38,plain,(
% 19.17/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.17/2.99    inference(rectify,[],[f37])).
% 19.17/2.99  
% 19.17/2.99  fof(f39,plain,(
% 19.17/2.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 19.17/2.99    introduced(choice_axiom,[])).
% 19.17/2.99  
% 19.17/2.99  fof(f40,plain,(
% 19.17/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.17/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 19.17/2.99  
% 19.17/2.99  fof(f68,plain,(
% 19.17/2.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.17/2.99    inference(cnf_transformation,[],[f40])).
% 19.17/2.99  
% 19.17/2.99  fof(f6,axiom,(
% 19.17/2.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f72,plain,(
% 19.17/2.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f6])).
% 19.17/2.99  
% 19.17/2.99  fof(f7,axiom,(
% 19.17/2.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f73,plain,(
% 19.17/2.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f7])).
% 19.17/2.99  
% 19.17/2.99  fof(f8,axiom,(
% 19.17/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f74,plain,(
% 19.17/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f8])).
% 19.17/2.99  
% 19.17/2.99  fof(f85,plain,(
% 19.17/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.17/2.99    inference(definition_unfolding,[],[f73,f74])).
% 19.17/2.99  
% 19.17/2.99  fof(f86,plain,(
% 19.17/2.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.17/2.99    inference(definition_unfolding,[],[f72,f85])).
% 19.17/2.99  
% 19.17/2.99  fof(f98,plain,(
% 19.17/2.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.17/2.99    inference(definition_unfolding,[],[f68,f86])).
% 19.17/2.99  
% 19.17/2.99  fof(f120,plain,(
% 19.17/2.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 19.17/2.99    inference(equality_resolution,[],[f98])).
% 19.17/2.99  
% 19.17/2.99  fof(f1,axiom,(
% 19.17/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f16,plain,(
% 19.17/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.17/2.99    inference(ennf_transformation,[],[f1])).
% 19.17/2.99  
% 19.17/2.99  fof(f21,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.17/2.99    inference(nnf_transformation,[],[f16])).
% 19.17/2.99  
% 19.17/2.99  fof(f22,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.17/2.99    inference(rectify,[],[f21])).
% 19.17/2.99  
% 19.17/2.99  fof(f23,plain,(
% 19.17/2.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.17/2.99    introduced(choice_axiom,[])).
% 19.17/2.99  
% 19.17/2.99  fof(f24,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.17/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 19.17/2.99  
% 19.17/2.99  fof(f48,plain,(
% 19.17/2.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f24])).
% 19.17/2.99  
% 19.17/2.99  fof(f9,axiom,(
% 19.17/2.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f41,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.17/2.99    inference(nnf_transformation,[],[f9])).
% 19.17/2.99  
% 19.17/2.99  fof(f42,plain,(
% 19.17/2.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.17/2.99    inference(flattening,[],[f41])).
% 19.17/2.99  
% 19.17/2.99  fof(f76,plain,(
% 19.17/2.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 19.17/2.99    inference(cnf_transformation,[],[f42])).
% 19.17/2.99  
% 19.17/2.99  fof(f100,plain,(
% 19.17/2.99    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 19.17/2.99    inference(definition_unfolding,[],[f76,f86])).
% 19.17/2.99  
% 19.17/2.99  fof(f122,plain,(
% 19.17/2.99    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 19.17/2.99    inference(equality_resolution,[],[f100])).
% 19.17/2.99  
% 19.17/2.99  fof(f14,conjecture,(
% 19.17/2.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f15,negated_conjecture,(
% 19.17/2.99    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.17/2.99    inference(negated_conjecture,[],[f14])).
% 19.17/2.99  
% 19.17/2.99  fof(f20,plain,(
% 19.17/2.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 19.17/2.99    inference(ennf_transformation,[],[f15])).
% 19.17/2.99  
% 19.17/2.99  fof(f46,plain,(
% 19.17/2.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 19.17/2.99    introduced(choice_axiom,[])).
% 19.17/2.99  
% 19.17/2.99  fof(f47,plain,(
% 19.17/2.99    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 19.17/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f46])).
% 19.17/2.99  
% 19.17/2.99  fof(f84,plain,(
% 19.17/2.99    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 19.17/2.99    inference(cnf_transformation,[],[f47])).
% 19.17/2.99  
% 19.17/2.99  fof(f105,plain,(
% 19.17/2.99    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 19.17/2.99    inference(definition_unfolding,[],[f84,f86])).
% 19.17/2.99  
% 19.17/2.99  fof(f83,plain,(
% 19.17/2.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 19.17/2.99    inference(cnf_transformation,[],[f45])).
% 19.17/2.99  
% 19.17/2.99  fof(f10,axiom,(
% 19.17/2.99    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f78,plain,(
% 19.17/2.99    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 19.17/2.99    inference(cnf_transformation,[],[f10])).
% 19.17/2.99  
% 19.17/2.99  fof(f102,plain,(
% 19.17/2.99    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 19.17/2.99    inference(definition_unfolding,[],[f78,f86])).
% 19.17/2.99  
% 19.17/2.99  fof(f12,axiom,(
% 19.17/2.99    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f81,plain,(
% 19.17/2.99    ( ! [X0] : (r1_tarski(k1_setfam_1(X0),k3_tarski(X0))) )),
% 19.17/2.99    inference(cnf_transformation,[],[f12])).
% 19.17/2.99  
% 19.17/2.99  fof(f3,axiom,(
% 19.17/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.17/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.17/2.99  
% 19.17/2.99  fof(f30,plain,(
% 19.17/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.17/2.99    inference(nnf_transformation,[],[f3])).
% 19.17/2.99  
% 19.17/2.99  fof(f31,plain,(
% 19.17/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.17/2.99    inference(flattening,[],[f30])).
% 19.17/2.99  
% 19.17/2.99  fof(f59,plain,(
% 19.17/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.17/2.99    inference(cnf_transformation,[],[f31])).
% 19.17/2.99  
% 19.17/2.99  fof(f57,plain,(
% 19.17/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.17/2.99    inference(cnf_transformation,[],[f31])).
% 19.17/2.99  
% 19.17/2.99  fof(f110,plain,(
% 19.17/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.17/2.99    inference(equality_resolution,[],[f57])).
% 19.17/2.99  
% 19.17/2.99  fof(f69,plain,(
% 19.17/2.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.17/2.99    inference(cnf_transformation,[],[f40])).
% 19.17/2.99  
% 19.17/2.99  fof(f97,plain,(
% 19.17/2.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.17/2.99    inference(definition_unfolding,[],[f69,f86])).
% 19.17/2.99  
% 19.17/2.99  fof(f118,plain,(
% 19.17/2.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 19.17/2.99    inference(equality_resolution,[],[f97])).
% 19.17/2.99  
% 19.17/2.99  fof(f119,plain,(
% 19.17/2.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 19.17/2.99    inference(equality_resolution,[],[f118])).
% 19.17/2.99  
% 19.17/2.99  cnf(c_32,plain,
% 19.17/2.99      ( r2_hidden(sK4(X0,X1),X0)
% 19.17/2.99      | r1_tarski(X1,k1_setfam_1(X0))
% 19.17/2.99      | k1_xboole_0 = X0 ),
% 19.17/2.99      inference(cnf_transformation,[],[f82]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_23,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 19.17/2.99      inference(cnf_transformation,[],[f120]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1952,plain,
% 19.17/2.99      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.17/2.99      | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 19.17/2.99      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_32,c_23]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_676,plain,
% 19.17/2.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.17/2.99      theory(equality) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_42282,plain,
% 19.17/2.99      ( ~ r1_tarski(X0,X1)
% 19.17/2.99      | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
% 19.17/2.99      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.17/2.99      | X2 != X0
% 19.17/2.99      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_1952,c_676]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_42304,plain,
% 19.17/2.99      ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 19.17/2.99      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 19.17/2.99      | ~ r1_tarski(sK5,sK5)
% 19.17/2.99      | sK5 != sK5
% 19.17/2.99      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_42282]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.17/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_25,plain,
% 19.17/2.99      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 19.17/2.99      inference(cnf_transformation,[],[f122]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2705,plain,
% 19.17/2.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
% 19.17/2.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_2,c_25]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_3219,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,k1_xboole_0) | X0 = X1 ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_2705,c_23]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_675,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_674,plain,( X0 = X0 ),theory(equality) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2172,plain,
% 19.17/2.99      ( X0 != X1 | X1 = X0 ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_675,c_674]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_3233,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,k1_xboole_0) | X1 = X0 ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_3219,c_2172]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_33,negated_conjecture,
% 19.17/2.99      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 19.17/2.99      inference(cnf_transformation,[],[f105]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_3621,plain,
% 19.17/2.99      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 19.17/2.99      inference(resolution,[status(thm)],[c_3233,c_33]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_31,plain,
% 19.17/2.99      ( ~ r1_tarski(X0,sK4(X1,X0))
% 19.17/2.99      | r1_tarski(X0,k1_setfam_1(X1))
% 19.17/2.99      | k1_xboole_0 = X1 ),
% 19.17/2.99      inference(cnf_transformation,[],[f83]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2129,plain,
% 19.17/2.99      ( ~ r1_tarski(X0,sK4(k2_enumset1(X1,X1,X2,X3),X0))
% 19.17/2.99      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
% 19.17/2.99      | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_31]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2133,plain,
% 19.17/2.99      ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 19.17/2.99      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 19.17/2.99      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_2129]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_677,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.17/2.99      theory(equality) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1507,plain,
% 19.17/2.99      ( r2_hidden(X0,X1)
% 19.17/2.99      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 19.17/2.99      | X0 != X2
% 19.17/2.99      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_677]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2070,plain,
% 19.17/2.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 19.17/2.99      | r2_hidden(X3,k1_xboole_0)
% 19.17/2.99      | X3 != X0
% 19.17/2.99      | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_1507]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_2074,plain,
% 19.17/2.99      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 19.17/2.99      | r2_hidden(sK5,k1_xboole_0)
% 19.17/2.99      | sK5 != sK5
% 19.17/2.99      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_2070]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_27,plain,
% 19.17/2.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 19.17/2.99      inference(cnf_transformation,[],[f102]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_30,plain,
% 19.17/2.99      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
% 19.17/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1360,plain,
% 19.17/2.99      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
% 19.17/2.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1528,plain,
% 19.17/2.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
% 19.17/2.99      inference(superposition,[status(thm)],[c_27,c_1360]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1529,plain,
% 19.17/2.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
% 19.17/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_1528]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1531,plain,
% 19.17/2.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_9,plain,
% 19.17/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.17/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_1472,plain,
% 19.17/2.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 19.17/2.99      | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 19.17/2.99      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_11,plain,
% 19.17/2.99      ( r1_tarski(X0,X0) ),
% 19.17/2.99      inference(cnf_transformation,[],[f110]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_84,plain,
% 19.17/2.99      ( r1_tarski(sK5,sK5) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_11]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_22,plain,
% 19.17/2.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 19.17/2.99      inference(cnf_transformation,[],[f119]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_63,plain,
% 19.17/2.99      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_22]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(c_60,plain,
% 19.17/2.99      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 19.17/2.99      inference(instantiation,[status(thm)],[c_23]) ).
% 19.17/2.99  
% 19.17/2.99  cnf(contradiction,plain,
% 19.17/2.99      ( $false ),
% 19.17/2.99      inference(minisat,
% 19.17/2.99                [status(thm)],
% 19.17/2.99                [c_42304,c_3621,c_2133,c_2074,c_1531,c_1472,c_84,c_63,
% 19.17/2.99                 c_60,c_33]) ).
% 19.17/2.99  
% 19.17/2.99  
% 19.17/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.17/2.99  
% 19.17/2.99  ------                               Statistics
% 19.17/2.99  
% 19.17/2.99  ------ Selected
% 19.17/2.99  
% 19.17/2.99  total_time:                             2.213
% 19.17/2.99  
%------------------------------------------------------------------------------
