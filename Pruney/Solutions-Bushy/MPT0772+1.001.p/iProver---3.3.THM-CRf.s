%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0772+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:05 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 456 expanded)
%              Number of clauses        :   55 ( 150 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   24
%              Number of atoms          :  354 (1878 expanded)
%              Number of equality atoms :  132 ( 495 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f26])).

fof(f45,plain,(
    ~ r1_tarski(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
          | sK0(X0,X1,X2) = X1
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
            & sK0(X0,X1,X2) != X1 )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                | sK0(X0,X1,X2) = X1
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                  & sK0(X0,X1,X2) != X1 )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f44,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f49,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_205,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_wellord1(k2_wellord1(sK5,sK3),sK4) != X0
    | k1_wellord1(sK5,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_206,plain,
    ( r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(k2_wellord1(sK5,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_618,plain,
    ( r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(k2_wellord1(sK5,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_629,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1125,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,sK3)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_629])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_619,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_621,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1072,plain,
    ( k3_xboole_0(sK5,k2_zfmisc_1(X0,X0)) = k2_wellord1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_619,c_621])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_623,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1415,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_623])).

cnf(c_1467,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_zfmisc_1(sK3,sK3)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1125,c_1415])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1071,plain,
    ( k3_xboole_0(k2_wellord1(X0,X1),k2_zfmisc_1(X2,X2)) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_621])).

cnf(c_2196,plain,
    ( k3_xboole_0(k2_wellord1(sK5,X0),k2_zfmisc_1(X1,X1)) = k2_wellord1(k2_wellord1(sK5,X0),X1) ),
    inference(superposition,[status(thm)],[c_619,c_1071])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_624,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2404,plain,
    ( r2_hidden(X0,k2_wellord1(k2_wellord1(sK5,X1),X2)) = iProver_top
    | r2_hidden(X0,k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_624])).

cnf(c_2524,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(k2_wellord1(sK5,X0),sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,X0)) != iProver_top
    | v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_2404])).

cnf(c_18,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1854,plain,
    ( v1_relat_1(k2_wellord1(sK5,sK3))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1855,plain,
    ( v1_relat_1(k2_wellord1(sK5,sK3)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1854])).

cnf(c_2965,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(k2_wellord1(sK5,X0),sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_18,c_1855])).

cnf(c_2966,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(k2_wellord1(sK5,X0),sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2965])).

cnf(c_2405,plain,
    ( r2_hidden(X0,k2_wellord1(k2_wellord1(sK5,X1),X2)) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X2,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_623])).

cnf(c_2973,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_zfmisc_1(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_2405])).

cnf(c_2981,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_zfmisc_1(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_18,c_1467,c_1855])).

cnf(c_1414,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X1)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_624])).

cnf(c_2986,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_1414])).

cnf(c_3160,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),k2_wellord1(sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_18,c_1125,c_1855])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_622,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1416,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_622])).

cnf(c_3166,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_1416])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_630,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3169,plain,
    ( sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) = sK4
    | r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(sK5,sK4)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_630])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_212,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | k1_wellord1(k2_wellord1(sK5,sK3),sK4) != X0
    | k1_wellord1(sK5,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_213,plain,
    ( ~ r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_1468,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),sK4),sK5) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1125,c_1416])).

cnf(c_1577,plain,
    ( sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) = sK4
    | r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(sK5,sK4)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_630])).

cnf(c_1578,plain,
    ( r2_hidden(sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)),k1_wellord1(sK5,sK4))
    | ~ v1_relat_1(k2_wellord1(sK5,sK3))
    | ~ v1_relat_1(sK5)
    | sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1577])).

cnf(c_11184,plain,
    ( sK1(k1_wellord1(k2_wellord1(sK5,sK3),sK4),k1_wellord1(sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3169,c_17,c_213,c_1578,c_1854])).

cnf(c_11192,plain,
    ( r2_hidden(sK4,k1_wellord1(k2_wellord1(sK5,sK3),sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11184,c_618])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_628,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11692,plain,
    ( v1_relat_1(k2_wellord1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11192,c_628])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11692,c_1855,c_18])).


%------------------------------------------------------------------------------
