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
% DateTime   : Thu Dec  3 11:44:15 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 387 expanded)
%              Number of clauses        :   50 ( 138 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   22
%              Number of atoms          :  336 (1405 expanded)
%              Number of equality atoms :  183 ( 439 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f31])).

fof(f48,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f23,f22])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_403,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_415,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_410,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_417,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1180,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
    | r2_hidden(k4_tarski(sK6(X0,X1,k3_xboole_0(X2,X3)),sK5(X0,X1,k3_xboole_0(X2,X3))),X1) = iProver_top
    | r1_xboole_0(X2,X3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_417])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_413,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_825,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_417])).

cnf(c_6914,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
    | r2_hidden(k4_tarski(sK6(X0,X1,k3_xboole_0(X2,X3)),sK5(X0,X1,k3_xboole_0(X2,X3))),X1) = iProver_top
    | r1_xboole_0(X2,X3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1180,c_825])).

cnf(c_6918,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,k1_xboole_0)
    | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_6914])).

cnf(c_6971,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6918,c_2])).

cnf(c_826,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_417])).

cnf(c_844,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_826,c_415])).

cnf(c_848,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_844])).

cnf(c_1182,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_844])).

cnf(c_7056,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6971,c_848,c_1182])).

cnf(c_7057,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7056])).

cnf(c_7064,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7057,c_417])).

cnf(c_1183,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
    | r2_hidden(k4_tarski(sK4(X0,k3_xboole_0(X1,X2),X3),sK5(X0,k3_xboole_0(X1,X2),X3)),X3) = iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_417])).

cnf(c_8125,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
    | r2_hidden(k4_tarski(sK4(X0,k3_xboole_0(X1,X2),X3),sK5(X0,k3_xboole_0(X1,X2),X3)),X3) = iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1183,c_825])).

cnf(c_8133,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8125,c_844])).

cnf(c_8564,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7064,c_848,c_8133])).

cnf(c_8565,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8564])).

cnf(c_8571,plain,
    ( k5_relat_1(X0,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_8565])).

cnf(c_8572,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8571,c_2])).

cnf(c_8578,plain,
    ( k5_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_403,c_8572])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_409,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1081,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
    | r2_hidden(k4_tarski(sK4(X0,X1,k3_xboole_0(X2,X3)),sK6(X0,X1,k3_xboole_0(X2,X3))),X0) = iProver_top
    | r1_xboole_0(X2,X3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_417])).

cnf(c_3526,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
    | r2_hidden(k4_tarski(sK4(X0,X1,k3_xboole_0(X2,X3)),sK6(X0,X1,k3_xboole_0(X2,X3))),X0) = iProver_top
    | r1_xboole_0(X2,X3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1081,c_825])).

cnf(c_3530,plain,
    ( k5_relat_1(X0,X1) = k3_xboole_0(X2,k1_xboole_0)
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_3526])).

cnf(c_3583,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3530,c_2])).

cnf(c_1083,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_844])).

cnf(c_3753,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3583,c_848,c_1083])).

cnf(c_3754,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3753])).

cnf(c_3761,plain,
    ( k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3754,c_417])).

cnf(c_4032,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_825])).

cnf(c_4033,plain,
    ( k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4032])).

cnf(c_4041,plain,
    ( k5_relat_1(k3_xboole_0(X0,k1_xboole_0),X1) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_4033])).

cnf(c_4042,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4041,c_2])).

cnf(c_4246,plain,
    ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_403,c_4042])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4436,plain,
    ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4246,c_15])).

cnf(c_4437,plain,
    ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4436])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8578,c_4437])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.99  
% 3.85/0.99  ------  iProver source info
% 3.85/0.99  
% 3.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.99  git: non_committed_changes: false
% 3.85/0.99  git: last_make_outside_of_git: false
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options
% 3.85/0.99  
% 3.85/0.99  --out_options                           all
% 3.85/0.99  --tptp_safe_out                         true
% 3.85/0.99  --problem_path                          ""
% 3.85/0.99  --include_path                          ""
% 3.85/0.99  --clausifier                            res/vclausify_rel
% 3.85/0.99  --clausifier_options                    --mode clausify
% 3.85/0.99  --stdin                                 false
% 3.85/0.99  --stats_out                             sel
% 3.85/0.99  
% 3.85/0.99  ------ General Options
% 3.85/0.99  
% 3.85/0.99  --fof                                   false
% 3.85/0.99  --time_out_real                         604.99
% 3.85/0.99  --time_out_virtual                      -1.
% 3.85/0.99  --symbol_type_check                     false
% 3.85/0.99  --clausify_out                          false
% 3.85/0.99  --sig_cnt_out                           false
% 3.85/0.99  --trig_cnt_out                          false
% 3.85/0.99  --trig_cnt_out_tolerance                1.
% 3.85/0.99  --trig_cnt_out_sk_spl                   false
% 3.85/0.99  --abstr_cl_out                          false
% 3.85/0.99  
% 3.85/0.99  ------ Global Options
% 3.85/0.99  
% 3.85/0.99  --schedule                              none
% 3.85/0.99  --add_important_lit                     false
% 3.85/0.99  --prop_solver_per_cl                    1000
% 3.85/0.99  --min_unsat_core                        false
% 3.85/0.99  --soft_assumptions                      false
% 3.85/0.99  --soft_lemma_size                       3
% 3.85/0.99  --prop_impl_unit_size                   0
% 3.85/0.99  --prop_impl_unit                        []
% 3.85/0.99  --share_sel_clauses                     true
% 3.85/0.99  --reset_solvers                         false
% 3.85/0.99  --bc_imp_inh                            [conj_cone]
% 3.85/0.99  --conj_cone_tolerance                   3.
% 3.85/0.99  --extra_neg_conj                        none
% 3.85/0.99  --large_theory_mode                     true
% 3.85/0.99  --prolific_symb_bound                   200
% 3.85/0.99  --lt_threshold                          2000
% 3.85/0.99  --clause_weak_htbl                      true
% 3.85/0.99  --gc_record_bc_elim                     false
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing Options
% 3.85/0.99  
% 3.85/0.99  --preprocessing_flag                    true
% 3.85/0.99  --time_out_prep_mult                    0.1
% 3.85/0.99  --splitting_mode                        input
% 3.85/0.99  --splitting_grd                         true
% 3.85/0.99  --splitting_cvd                         false
% 3.85/0.99  --splitting_cvd_svl                     false
% 3.85/0.99  --splitting_nvd                         32
% 3.85/0.99  --sub_typing                            true
% 3.85/0.99  --prep_gs_sim                           false
% 3.85/0.99  --prep_unflatten                        true
% 3.85/0.99  --prep_res_sim                          true
% 3.85/0.99  --prep_upred                            true
% 3.85/0.99  --prep_sem_filter                       exhaustive
% 3.85/0.99  --prep_sem_filter_out                   false
% 3.85/0.99  --pred_elim                             false
% 3.85/0.99  --res_sim_input                         true
% 3.85/0.99  --eq_ax_congr_red                       true
% 3.85/0.99  --pure_diseq_elim                       true
% 3.85/0.99  --brand_transform                       false
% 3.85/0.99  --non_eq_to_eq                          false
% 3.85/0.99  --prep_def_merge                        true
% 3.85/0.99  --prep_def_merge_prop_impl              false
% 3.85/0.99  --prep_def_merge_mbd                    true
% 3.85/0.99  --prep_def_merge_tr_red                 false
% 3.85/0.99  --prep_def_merge_tr_cl                  false
% 3.85/0.99  --smt_preprocessing                     true
% 3.85/0.99  --smt_ac_axioms                         fast
% 3.85/0.99  --preprocessed_out                      false
% 3.85/0.99  --preprocessed_stats                    false
% 3.85/0.99  
% 3.85/0.99  ------ Abstraction refinement Options
% 3.85/0.99  
% 3.85/0.99  --abstr_ref                             []
% 3.85/0.99  --abstr_ref_prep                        false
% 3.85/0.99  --abstr_ref_until_sat                   false
% 3.85/0.99  --abstr_ref_sig_restrict                funpre
% 3.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.99  --abstr_ref_under                       []
% 3.85/0.99  
% 3.85/0.99  ------ SAT Options
% 3.85/0.99  
% 3.85/0.99  --sat_mode                              false
% 3.85/0.99  --sat_fm_restart_options                ""
% 3.85/0.99  --sat_gr_def                            false
% 3.85/0.99  --sat_epr_types                         true
% 3.85/0.99  --sat_non_cyclic_types                  false
% 3.85/0.99  --sat_finite_models                     false
% 3.85/0.99  --sat_fm_lemmas                         false
% 3.85/0.99  --sat_fm_prep                           false
% 3.85/0.99  --sat_fm_uc_incr                        true
% 3.85/0.99  --sat_out_model                         small
% 3.85/0.99  --sat_out_clauses                       false
% 3.85/0.99  
% 3.85/0.99  ------ QBF Options
% 3.85/0.99  
% 3.85/0.99  --qbf_mode                              false
% 3.85/0.99  --qbf_elim_univ                         false
% 3.85/0.99  --qbf_dom_inst                          none
% 3.85/0.99  --qbf_dom_pre_inst                      false
% 3.85/0.99  --qbf_sk_in                             false
% 3.85/0.99  --qbf_pred_elim                         true
% 3.85/0.99  --qbf_split                             512
% 3.85/0.99  
% 3.85/0.99  ------ BMC1 Options
% 3.85/0.99  
% 3.85/0.99  --bmc1_incremental                      false
% 3.85/0.99  --bmc1_axioms                           reachable_all
% 3.85/0.99  --bmc1_min_bound                        0
% 3.85/0.99  --bmc1_max_bound                        -1
% 3.85/0.99  --bmc1_max_bound_default                -1
% 3.85/0.99  --bmc1_symbol_reachability              true
% 3.85/0.99  --bmc1_property_lemmas                  false
% 3.85/0.99  --bmc1_k_induction                      false
% 3.85/0.99  --bmc1_non_equiv_states                 false
% 3.85/0.99  --bmc1_deadlock                         false
% 3.85/0.99  --bmc1_ucm                              false
% 3.85/0.99  --bmc1_add_unsat_core                   none
% 3.85/0.99  --bmc1_unsat_core_children              false
% 3.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.99  --bmc1_out_stat                         full
% 3.85/0.99  --bmc1_ground_init                      false
% 3.85/0.99  --bmc1_pre_inst_next_state              false
% 3.85/0.99  --bmc1_pre_inst_state                   false
% 3.85/0.99  --bmc1_pre_inst_reach_state             false
% 3.85/0.99  --bmc1_out_unsat_core                   false
% 3.85/0.99  --bmc1_aig_witness_out                  false
% 3.85/0.99  --bmc1_verbose                          false
% 3.85/0.99  --bmc1_dump_clauses_tptp                false
% 3.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.99  --bmc1_dump_file                        -
% 3.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.99  --bmc1_ucm_extend_mode                  1
% 3.85/0.99  --bmc1_ucm_init_mode                    2
% 3.85/0.99  --bmc1_ucm_cone_mode                    none
% 3.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.99  --bmc1_ucm_relax_model                  4
% 3.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.99  --bmc1_ucm_layered_model                none
% 3.85/0.99  --bmc1_ucm_max_lemma_size               10
% 3.85/0.99  
% 3.85/0.99  ------ AIG Options
% 3.85/0.99  
% 3.85/0.99  --aig_mode                              false
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation Options
% 3.85/0.99  
% 3.85/0.99  --instantiation_flag                    true
% 3.85/0.99  --inst_sos_flag                         false
% 3.85/0.99  --inst_sos_phase                        true
% 3.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel_side                     num_symb
% 3.85/0.99  --inst_solver_per_active                1400
% 3.85/0.99  --inst_solver_calls_frac                1.
% 3.85/0.99  --inst_passive_queue_type               priority_queues
% 3.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.99  --inst_passive_queues_freq              [25;2]
% 3.85/0.99  --inst_dismatching                      true
% 3.85/0.99  --inst_eager_unprocessed_to_passive     true
% 3.85/0.99  --inst_prop_sim_given                   true
% 3.85/0.99  --inst_prop_sim_new                     false
% 3.85/0.99  --inst_subs_new                         false
% 3.85/0.99  --inst_eq_res_simp                      false
% 3.85/0.99  --inst_subs_given                       false
% 3.85/0.99  --inst_orphan_elimination               true
% 3.85/0.99  --inst_learning_loop_flag               true
% 3.85/0.99  --inst_learning_start                   3000
% 3.85/0.99  --inst_learning_factor                  2
% 3.85/0.99  --inst_start_prop_sim_after_learn       3
% 3.85/0.99  --inst_sel_renew                        solver
% 3.85/0.99  --inst_lit_activity_flag                true
% 3.85/0.99  --inst_restr_to_given                   false
% 3.85/0.99  --inst_activity_threshold               500
% 3.85/0.99  --inst_out_proof                        true
% 3.85/0.99  
% 3.85/0.99  ------ Resolution Options
% 3.85/0.99  
% 3.85/0.99  --resolution_flag                       true
% 3.85/0.99  --res_lit_sel                           adaptive
% 3.85/0.99  --res_lit_sel_side                      none
% 3.85/0.99  --res_ordering                          kbo
% 3.85/0.99  --res_to_prop_solver                    active
% 3.85/0.99  --res_prop_simpl_new                    false
% 3.85/0.99  --res_prop_simpl_given                  true
% 3.85/0.99  --res_passive_queue_type                priority_queues
% 3.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.99  --res_passive_queues_freq               [15;5]
% 3.85/0.99  --res_forward_subs                      full
% 3.85/0.99  --res_backward_subs                     full
% 3.85/0.99  --res_forward_subs_resolution           true
% 3.85/0.99  --res_backward_subs_resolution          true
% 3.85/0.99  --res_orphan_elimination                true
% 3.85/0.99  --res_time_limit                        2.
% 3.85/0.99  --res_out_proof                         true
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Options
% 3.85/0.99  
% 3.85/0.99  --superposition_flag                    true
% 3.85/0.99  --sup_passive_queue_type                priority_queues
% 3.85/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.99  --sup_passive_queues_freq               [1;4]
% 3.85/0.99  --demod_completeness_check              fast
% 3.85/0.99  --demod_use_ground                      true
% 3.85/0.99  --sup_to_prop_solver                    passive
% 3.85/0.99  --sup_prop_simpl_new                    true
% 3.85/0.99  --sup_prop_simpl_given                  true
% 3.85/0.99  --sup_fun_splitting                     false
% 3.85/0.99  --sup_smt_interval                      50000
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Simplification Setup
% 3.85/0.99  
% 3.85/0.99  --sup_indices_passive                   []
% 3.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_full_bw                           [BwDemod]
% 3.85/0.99  --sup_immed_triv                        [TrivRules]
% 3.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_immed_bw_main                     []
% 3.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.99  
% 3.85/0.99  ------ Combination Options
% 3.85/0.99  
% 3.85/0.99  --comb_res_mult                         3
% 3.85/0.99  --comb_sup_mult                         2
% 3.85/0.99  --comb_inst_mult                        10
% 3.85/0.99  
% 3.85/0.99  ------ Debug Options
% 3.85/0.99  
% 3.85/0.99  --dbg_backtrace                         false
% 3.85/0.99  --dbg_dump_prop_clauses                 false
% 3.85/0.99  --dbg_dump_prop_clauses_file            -
% 3.85/0.99  --dbg_out_stat                          false
% 3.85/0.99  ------ Parsing...
% 3.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.99  ------ Proving...
% 3.85/0.99  ------ Problem Properties 
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  clauses                                 17
% 3.85/0.99  conjectures                             2
% 3.85/0.99  EPR                                     2
% 3.85/0.99  Horn                                    13
% 3.85/0.99  unary                                   3
% 3.85/0.99  binary                                  5
% 3.85/0.99  lits                                    58
% 3.85/0.99  lits eq                                 9
% 3.85/0.99  fd_pure                                 0
% 3.85/0.99  fd_pseudo                               0
% 3.85/0.99  fd_cond                                 0
% 3.85/0.99  fd_pseudo_cond                          3
% 3.85/0.99  AC symbols                              0
% 3.85/0.99  
% 3.85/0.99  ------ Input Options Time Limit: Unbounded
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  Current options:
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options
% 3.85/0.99  
% 3.85/0.99  --out_options                           all
% 3.85/0.99  --tptp_safe_out                         true
% 3.85/0.99  --problem_path                          ""
% 3.85/0.99  --include_path                          ""
% 3.85/0.99  --clausifier                            res/vclausify_rel
% 3.85/0.99  --clausifier_options                    --mode clausify
% 3.85/0.99  --stdin                                 false
% 3.85/0.99  --stats_out                             sel
% 3.85/0.99  
% 3.85/0.99  ------ General Options
% 3.85/0.99  
% 3.85/0.99  --fof                                   false
% 3.85/0.99  --time_out_real                         604.99
% 3.85/0.99  --time_out_virtual                      -1.
% 3.85/0.99  --symbol_type_check                     false
% 3.85/0.99  --clausify_out                          false
% 3.85/0.99  --sig_cnt_out                           false
% 3.85/0.99  --trig_cnt_out                          false
% 3.85/0.99  --trig_cnt_out_tolerance                1.
% 3.85/0.99  --trig_cnt_out_sk_spl                   false
% 3.85/0.99  --abstr_cl_out                          false
% 3.85/0.99  
% 3.85/0.99  ------ Global Options
% 3.85/0.99  
% 3.85/0.99  --schedule                              none
% 3.85/0.99  --add_important_lit                     false
% 3.85/0.99  --prop_solver_per_cl                    1000
% 3.85/0.99  --min_unsat_core                        false
% 3.85/0.99  --soft_assumptions                      false
% 3.85/0.99  --soft_lemma_size                       3
% 3.85/0.99  --prop_impl_unit_size                   0
% 3.85/0.99  --prop_impl_unit                        []
% 3.85/0.99  --share_sel_clauses                     true
% 3.85/0.99  --reset_solvers                         false
% 3.85/0.99  --bc_imp_inh                            [conj_cone]
% 3.85/0.99  --conj_cone_tolerance                   3.
% 3.85/0.99  --extra_neg_conj                        none
% 3.85/0.99  --large_theory_mode                     true
% 3.85/0.99  --prolific_symb_bound                   200
% 3.85/0.99  --lt_threshold                          2000
% 3.85/0.99  --clause_weak_htbl                      true
% 3.85/0.99  --gc_record_bc_elim                     false
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing Options
% 3.85/0.99  
% 3.85/0.99  --preprocessing_flag                    true
% 3.85/0.99  --time_out_prep_mult                    0.1
% 3.85/0.99  --splitting_mode                        input
% 3.85/0.99  --splitting_grd                         true
% 3.85/0.99  --splitting_cvd                         false
% 3.85/0.99  --splitting_cvd_svl                     false
% 3.85/0.99  --splitting_nvd                         32
% 3.85/0.99  --sub_typing                            true
% 3.85/0.99  --prep_gs_sim                           false
% 3.85/0.99  --prep_unflatten                        true
% 3.85/0.99  --prep_res_sim                          true
% 3.85/0.99  --prep_upred                            true
% 3.85/0.99  --prep_sem_filter                       exhaustive
% 3.85/0.99  --prep_sem_filter_out                   false
% 3.85/0.99  --pred_elim                             false
% 3.85/0.99  --res_sim_input                         true
% 3.85/0.99  --eq_ax_congr_red                       true
% 3.85/0.99  --pure_diseq_elim                       true
% 3.85/0.99  --brand_transform                       false
% 3.85/0.99  --non_eq_to_eq                          false
% 3.85/0.99  --prep_def_merge                        true
% 3.85/0.99  --prep_def_merge_prop_impl              false
% 3.85/0.99  --prep_def_merge_mbd                    true
% 3.85/0.99  --prep_def_merge_tr_red                 false
% 3.85/0.99  --prep_def_merge_tr_cl                  false
% 3.85/0.99  --smt_preprocessing                     true
% 3.85/0.99  --smt_ac_axioms                         fast
% 3.85/0.99  --preprocessed_out                      false
% 3.85/0.99  --preprocessed_stats                    false
% 3.85/0.99  
% 3.85/0.99  ------ Abstraction refinement Options
% 3.85/0.99  
% 3.85/0.99  --abstr_ref                             []
% 3.85/0.99  --abstr_ref_prep                        false
% 3.85/0.99  --abstr_ref_until_sat                   false
% 3.85/0.99  --abstr_ref_sig_restrict                funpre
% 3.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.99  --abstr_ref_under                       []
% 3.85/0.99  
% 3.85/0.99  ------ SAT Options
% 3.85/0.99  
% 3.85/0.99  --sat_mode                              false
% 3.85/0.99  --sat_fm_restart_options                ""
% 3.85/0.99  --sat_gr_def                            false
% 3.85/0.99  --sat_epr_types                         true
% 3.85/0.99  --sat_non_cyclic_types                  false
% 3.85/0.99  --sat_finite_models                     false
% 3.85/0.99  --sat_fm_lemmas                         false
% 3.85/0.99  --sat_fm_prep                           false
% 3.85/0.99  --sat_fm_uc_incr                        true
% 3.85/0.99  --sat_out_model                         small
% 3.85/0.99  --sat_out_clauses                       false
% 3.85/0.99  
% 3.85/0.99  ------ QBF Options
% 3.85/0.99  
% 3.85/0.99  --qbf_mode                              false
% 3.85/0.99  --qbf_elim_univ                         false
% 3.85/0.99  --qbf_dom_inst                          none
% 3.85/0.99  --qbf_dom_pre_inst                      false
% 3.85/0.99  --qbf_sk_in                             false
% 3.85/0.99  --qbf_pred_elim                         true
% 3.85/0.99  --qbf_split                             512
% 3.85/0.99  
% 3.85/0.99  ------ BMC1 Options
% 3.85/0.99  
% 3.85/0.99  --bmc1_incremental                      false
% 3.85/0.99  --bmc1_axioms                           reachable_all
% 3.85/0.99  --bmc1_min_bound                        0
% 3.85/0.99  --bmc1_max_bound                        -1
% 3.85/0.99  --bmc1_max_bound_default                -1
% 3.85/0.99  --bmc1_symbol_reachability              true
% 3.85/0.99  --bmc1_property_lemmas                  false
% 3.85/0.99  --bmc1_k_induction                      false
% 3.85/0.99  --bmc1_non_equiv_states                 false
% 3.85/0.99  --bmc1_deadlock                         false
% 3.85/0.99  --bmc1_ucm                              false
% 3.85/0.99  --bmc1_add_unsat_core                   none
% 3.85/0.99  --bmc1_unsat_core_children              false
% 3.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.99  --bmc1_out_stat                         full
% 3.85/0.99  --bmc1_ground_init                      false
% 3.85/0.99  --bmc1_pre_inst_next_state              false
% 3.85/0.99  --bmc1_pre_inst_state                   false
% 3.85/0.99  --bmc1_pre_inst_reach_state             false
% 3.85/0.99  --bmc1_out_unsat_core                   false
% 3.85/0.99  --bmc1_aig_witness_out                  false
% 3.85/0.99  --bmc1_verbose                          false
% 3.85/0.99  --bmc1_dump_clauses_tptp                false
% 3.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.99  --bmc1_dump_file                        -
% 3.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.99  --bmc1_ucm_extend_mode                  1
% 3.85/0.99  --bmc1_ucm_init_mode                    2
% 3.85/0.99  --bmc1_ucm_cone_mode                    none
% 3.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.99  --bmc1_ucm_relax_model                  4
% 3.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.99  --bmc1_ucm_layered_model                none
% 3.85/0.99  --bmc1_ucm_max_lemma_size               10
% 3.85/0.99  
% 3.85/0.99  ------ AIG Options
% 3.85/0.99  
% 3.85/0.99  --aig_mode                              false
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation Options
% 3.85/0.99  
% 3.85/0.99  --instantiation_flag                    true
% 3.85/0.99  --inst_sos_flag                         false
% 3.85/0.99  --inst_sos_phase                        true
% 3.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel_side                     num_symb
% 3.85/0.99  --inst_solver_per_active                1400
% 3.85/0.99  --inst_solver_calls_frac                1.
% 3.85/0.99  --inst_passive_queue_type               priority_queues
% 3.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.99  --inst_passive_queues_freq              [25;2]
% 3.85/0.99  --inst_dismatching                      true
% 3.85/0.99  --inst_eager_unprocessed_to_passive     true
% 3.85/0.99  --inst_prop_sim_given                   true
% 3.85/0.99  --inst_prop_sim_new                     false
% 3.85/0.99  --inst_subs_new                         false
% 3.85/0.99  --inst_eq_res_simp                      false
% 3.85/0.99  --inst_subs_given                       false
% 3.85/0.99  --inst_orphan_elimination               true
% 3.85/0.99  --inst_learning_loop_flag               true
% 3.85/0.99  --inst_learning_start                   3000
% 3.85/0.99  --inst_learning_factor                  2
% 3.85/0.99  --inst_start_prop_sim_after_learn       3
% 3.85/0.99  --inst_sel_renew                        solver
% 3.85/0.99  --inst_lit_activity_flag                true
% 3.85/0.99  --inst_restr_to_given                   false
% 3.85/0.99  --inst_activity_threshold               500
% 3.85/0.99  --inst_out_proof                        true
% 3.85/0.99  
% 3.85/0.99  ------ Resolution Options
% 3.85/0.99  
% 3.85/0.99  --resolution_flag                       true
% 3.85/0.99  --res_lit_sel                           adaptive
% 3.85/0.99  --res_lit_sel_side                      none
% 3.85/0.99  --res_ordering                          kbo
% 3.85/0.99  --res_to_prop_solver                    active
% 3.85/0.99  --res_prop_simpl_new                    false
% 3.85/0.99  --res_prop_simpl_given                  true
% 3.85/0.99  --res_passive_queue_type                priority_queues
% 3.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.99  --res_passive_queues_freq               [15;5]
% 3.85/0.99  --res_forward_subs                      full
% 3.85/0.99  --res_backward_subs                     full
% 3.85/0.99  --res_forward_subs_resolution           true
% 3.85/0.99  --res_backward_subs_resolution          true
% 3.85/0.99  --res_orphan_elimination                true
% 3.85/0.99  --res_time_limit                        2.
% 3.85/0.99  --res_out_proof                         true
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Options
% 3.85/0.99  
% 3.85/0.99  --superposition_flag                    true
% 3.85/0.99  --sup_passive_queue_type                priority_queues
% 3.85/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.99  --sup_passive_queues_freq               [1;4]
% 3.85/0.99  --demod_completeness_check              fast
% 3.85/0.99  --demod_use_ground                      true
% 3.85/0.99  --sup_to_prop_solver                    passive
% 3.85/0.99  --sup_prop_simpl_new                    true
% 3.85/0.99  --sup_prop_simpl_given                  true
% 3.85/0.99  --sup_fun_splitting                     false
% 3.85/0.99  --sup_smt_interval                      50000
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Simplification Setup
% 3.85/0.99  
% 3.85/0.99  --sup_indices_passive                   []
% 3.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_full_bw                           [BwDemod]
% 3.85/0.99  --sup_immed_triv                        [TrivRules]
% 3.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_immed_bw_main                     []
% 3.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.99  
% 3.85/0.99  ------ Combination Options
% 3.85/0.99  
% 3.85/0.99  --comb_res_mult                         3
% 3.85/0.99  --comb_sup_mult                         2
% 3.85/0.99  --comb_inst_mult                        10
% 3.85/0.99  
% 3.85/0.99  ------ Debug Options
% 3.85/0.99  
% 3.85/0.99  --dbg_backtrace                         false
% 3.85/0.99  --dbg_dump_prop_clauses                 false
% 3.85/0.99  --dbg_dump_prop_clauses_file            -
% 3.85/0.99  --dbg_out_stat                          false
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ Proving...
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS status Theorem for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  fof(f8,conjecture,(
% 3.85/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f9,negated_conjecture,(
% 3.85/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.85/0.99    inference(negated_conjecture,[],[f8])).
% 3.85/0.99  
% 3.85/0.99  fof(f17,plain,(
% 3.85/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f9])).
% 3.85/0.99  
% 3.85/0.99  fof(f31,plain,(
% 3.85/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f32,plain,(
% 3.85/0.99    (k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8)),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f31])).
% 3.85/0.99  
% 3.85/0.99  fof(f48,plain,(
% 3.85/0.99    v1_relat_1(sK8)),
% 3.85/0.99    inference(cnf_transformation,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  fof(f3,axiom,(
% 3.85/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f36,plain,(
% 3.85/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f3])).
% 3.85/0.99  
% 3.85/0.99  fof(f2,axiom,(
% 3.85/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f35,plain,(
% 3.85/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.85/0.99    inference(cnf_transformation,[],[f2])).
% 3.85/0.99  
% 3.85/0.99  fof(f5,axiom,(
% 3.85/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f13,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f5])).
% 3.85/0.99  
% 3.85/0.99  fof(f25,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.85/0.99    inference(nnf_transformation,[],[f13])).
% 3.85/0.99  
% 3.85/0.99  fof(f26,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.85/0.99    inference(rectify,[],[f25])).
% 3.85/0.99  
% 3.85/0.99  fof(f29,plain,(
% 3.85/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f28,plain,(
% 3.85/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0)))) )),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f27,plain,(
% 3.85/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f30,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).
% 3.85/0.99  
% 3.85/0.99  fof(f44,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f1,axiom,(
% 3.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f10,plain,(
% 3.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(rectify,[],[f1])).
% 3.85/0.99  
% 3.85/0.99  fof(f11,plain,(
% 3.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(ennf_transformation,[],[f10])).
% 3.85/0.99  
% 3.85/0.99  fof(f18,plain,(
% 3.85/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f19,plain,(
% 3.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 3.85/0.99  
% 3.85/0.99  fof(f34,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f19])).
% 3.85/0.99  
% 3.85/0.99  fof(f4,axiom,(
% 3.85/0.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f12,plain,(
% 3.85/0.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f4])).
% 3.85/0.99  
% 3.85/0.99  fof(f20,plain,(
% 3.85/0.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 3.85/0.99    inference(nnf_transformation,[],[f12])).
% 3.85/0.99  
% 3.85/0.99  fof(f21,plain,(
% 3.85/0.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.85/0.99    inference(rectify,[],[f20])).
% 3.85/0.99  
% 3.85/0.99  fof(f23,plain,(
% 3.85/0.99    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f22,plain,(
% 3.85/0.99    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f24,plain,(
% 3.85/0.99    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f23,f22])).
% 3.85/0.99  
% 3.85/0.99  fof(f38,plain,(
% 3.85/0.99    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f24])).
% 3.85/0.99  
% 3.85/0.99  fof(f43,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f49,plain,(
% 3.85/0.99    k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)),
% 3.85/0.99    inference(cnf_transformation,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  cnf(c_16,negated_conjecture,
% 3.85/0.99      ( v1_relat_1(sK8) ),
% 3.85/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_403,plain,
% 3.85/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3,plain,
% 3.85/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_415,plain,
% 3.85/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2,plain,
% 3.85/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8,plain,
% 3.85/0.99      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
% 3.85/0.99      | ~ v1_relat_1(X0)
% 3.85/0.99      | ~ v1_relat_1(X1)
% 3.85/0.99      | ~ v1_relat_1(X2)
% 3.85/0.99      | k5_relat_1(X0,X1) = X2 ),
% 3.85/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_410,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = X2
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) = iProver_top
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_0,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_417,plain,
% 3.85/0.99      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1180,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k3_xboole_0(X2,X3)),sK5(X0,X1,k3_xboole_0(X2,X3))),X1) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,X3) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X2,X3)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_410,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5,plain,
% 3.85/0.99      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_413,plain,
% 3.85/0.99      ( r2_hidden(sK1(X0),X0) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_825,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_413,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6914,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k3_xboole_0(X2,X3)),sK5(X0,X1,k3_xboole_0(X2,X3))),X1) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,X3) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1180,c_825]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6918,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,k1_xboole_0)
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2,c_6914]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6971,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_6918,c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_826,plain,
% 3.85/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.85/0.99      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_844,plain,
% 3.85/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_826,c_415]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_848,plain,
% 3.85/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_413,c_844]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1182,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_410,c_844]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7056,plain,
% 3.85/0.99      ( r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.85/0.99      | k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_6971,c_848,c_1182]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7057,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK6(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_7056]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7064,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_7057,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1183,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,k3_xboole_0(X1,X2),X3),sK5(X0,k3_xboole_0(X1,X2),X3)),X3) = iProver_top
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X3) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_410,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8125,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,k3_xboole_0(X1,X2),X3),sK5(X0,k3_xboole_0(X1,X2),X3)),X3) = iProver_top
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1183,c_825]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8133,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_8125,c_844]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8564,plain,
% 3.85/0.99      ( v1_relat_1(X0) != iProver_top
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_7064,c_848,c_8133]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8565,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_8564]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8571,plain,
% 3.85/0.99      ( k5_relat_1(X0,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_415,c_8565]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8572,plain,
% 3.85/0.99      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_8571,c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8578,plain,
% 3.85/0.99      ( k5_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_403,c_8572]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_9,plain,
% 3.85/0.99      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
% 3.85/0.99      | ~ v1_relat_1(X0)
% 3.85/0.99      | ~ v1_relat_1(X1)
% 3.85/0.99      | ~ v1_relat_1(X2)
% 3.85/0.99      | k5_relat_1(X0,X1) = X2 ),
% 3.85/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_409,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = X2
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) = iProver_top
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1081,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k3_xboole_0(X2,X3)),sK6(X0,X1,k3_xboole_0(X2,X3))),X0) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,X3) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X2,X3)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_409,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3526,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,X3)
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k3_xboole_0(X2,X3)),sK6(X0,X1,k3_xboole_0(X2,X3))),X0) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,X3) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1081,c_825]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3530,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k3_xboole_0(X2,k1_xboole_0)
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2,c_3526]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3583,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.85/0.99      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_3530,c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1083,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top
% 3.85/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_409,c_844]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3753,plain,
% 3.85/0.99      ( r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.85/0.99      | k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_3583,c_848,c_1083]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3754,plain,
% 3.85/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK6(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.85/0.99      | v1_relat_1(X0) != iProver_top
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_3753]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3761,plain,
% 3.85/0.99      ( k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.99      | v1_relat_1(X2) != iProver_top
% 3.85/0.99      | v1_relat_1(k3_xboole_0(X0,X1)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3754,c_417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4032,plain,
% 3.85/0.99      ( v1_relat_1(X2) != iProver_top
% 3.85/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.99      | k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_3761,c_825]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4033,plain,
% 3.85/0.99      ( k5_relat_1(k3_xboole_0(X0,X1),X2) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_4032]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4041,plain,
% 3.85/0.99      ( k5_relat_1(k3_xboole_0(X0,k1_xboole_0),X1) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_415,c_4033]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4042,plain,
% 3.85/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.85/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.85/0.99      inference(light_normalisation,[status(thm)],[c_4041,c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4246,plain,
% 3.85/0.99      ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_403,c_4042]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15,negated_conjecture,
% 3.85/0.99      ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
% 3.85/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
% 3.85/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4436,plain,
% 3.85/0.99      ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0
% 3.85/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_4246,c_15]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4437,plain,
% 3.85/0.99      ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0 ),
% 3.85/0.99      inference(equality_resolution_simp,[status(thm)],[c_4436]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(contradiction,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(minisat,[status(thm)],[c_8578,c_4437]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ Selected
% 3.85/0.99  
% 3.85/0.99  total_time:                             0.38
% 3.85/0.99  
%------------------------------------------------------------------------------
