%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0600+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:41 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 318 expanded)
%              Number of clauses        :   48 (  93 expanded)
%              Number of leaves         :   11 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  303 (1443 expanded)
%              Number of equality atoms :  103 ( 280 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
        | ~ r2_hidden(k4_tarski(sK4,sK5),sK6) )
      & ( r2_hidden(sK5,k11_relat_1(sK6,sK4))
        | r2_hidden(k4_tarski(sK4,sK5),sK6) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
      | ~ r2_hidden(k4_tarski(sK4,sK5),sK6) )
    & ( r2_hidden(sK5,k11_relat_1(sK6,sK4))
      | r2_hidden(k4_tarski(sK4,sK5),sK6) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f21])).

fof(f35,plain,
    ( r2_hidden(sK5,k11_relat_1(sK6,sK4))
    | r2_hidden(k4_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13,f12,f11])).

fof(f25,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f34,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f41,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f40])).

fof(f23,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f36,plain,
    ( ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
    | ~ r2_hidden(k4_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6)
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_742,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6) = iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK6) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_738,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_966,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_738])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_736,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_744,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1086,plain,
    ( sK2(sK6,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k9_relat_1(sK6,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_744])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_197,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_198,plain,
    ( k9_relat_1(sK6,k1_tarski(X0)) = k11_relat_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_1089,plain,
    ( sK2(sK6,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k11_relat_1(sK6,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1086,c_198])).

cnf(c_1424,plain,
    ( sK2(sK6,k1_tarski(sK4),sK5) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_1089])).

cnf(c_953,plain,
    ( r2_hidden(sK2(sK6,k1_tarski(sK4),sK5),k1_tarski(sK4))
    | ~ r2_hidden(sK5,k9_relat_1(sK6,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_989,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_434,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1192,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_993,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
    | X1 != k11_relat_1(sK6,sK4)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_1191,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
    | X0 != k11_relat_1(sK6,sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1334,plain,
    ( ~ r2_hidden(sK5,k11_relat_1(sK6,sK4))
    | r2_hidden(sK5,k9_relat_1(sK6,k1_tarski(sK4)))
    | k9_relat_1(sK6,k1_tarski(sK4)) != k11_relat_1(sK6,sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_1335,plain,
    ( k9_relat_1(sK6,k1_tarski(sK4)) = k11_relat_1(sK6,sK4) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_1423,plain,
    ( r2_hidden(sK4,k1_tarski(X0)) != iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_198,c_966])).

cnf(c_1512,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1423])).

cnf(c_1514,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1512])).

cnf(c_1537,plain,
    ( ~ r2_hidden(sK4,k1_tarski(sK4))
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1514])).

cnf(c_1036,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK4))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1757,plain,
    ( ~ r2_hidden(sK2(sK6,k1_tarski(sK4),X0),k1_tarski(sK4))
    | sK2(sK6,k1_tarski(sK4),X0) = sK4 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2331,plain,
    ( ~ r2_hidden(sK2(sK6,k1_tarski(sK4),sK5),k1_tarski(sK4))
    | sK2(sK6,k1_tarski(sK4),sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_6650,plain,
    ( sK2(sK6,k1_tarski(sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1424,c_953,c_989,c_1192,c_1334,c_1335,c_1537,c_2331])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(sK2(sK6,X1,X0),X0),sK6) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_737,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK6,X1,X0),X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_6655,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,k1_tarski(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6650,c_737])).

cnf(c_6662,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6) = iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6655,c_198])).

cnf(c_990,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),sK6)
    | ~ r2_hidden(sK5,k11_relat_1(sK6,sK4)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6) != iProver_top
    | r2_hidden(sK5,k11_relat_1(sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6662,c_1514,c_990,c_16])).


%------------------------------------------------------------------------------
