%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:53 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 208 expanded)
%              Number of clauses        :   39 (  57 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  297 ( 626 expanded)
%              Number of equality atoms :   77 ( 139 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK4)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK4)))
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK3,X1)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK4)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f29,f28])).

fof(f52,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK4)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ~ r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(definition_unfolding,[],[f52,f47,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f47,f47])).

fof(f51,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f50,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_215,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) != X1
    | k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_216,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_10844,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10848,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10850,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10849,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11026,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK4,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10848,c_10849])).

cnf(c_11125,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_relat_1(k2_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,X1))))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10850,c_11026])).

cnf(c_11498,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k1_relat_1(k2_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) ),
    inference(superposition,[status(thm)],[c_10848,c_11125])).

cnf(c_15,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11513,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_11498,c_15])).

cnf(c_11571,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_0,c_11513])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10856,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11673,plain,
    ( r2_hidden(X0,k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,sK4)))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11571,c_10856])).

cnf(c_22346,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10844,c_11673])).

cnf(c_11053,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_10850])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10847,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11027,plain,
    ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10847,c_10849])).

cnf(c_11319,plain,
    ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1))))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11053,c_11027])).

cnf(c_13116,plain,
    ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) = k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) ),
    inference(superposition,[status(thm)],[c_10848,c_11319])).

cnf(c_13239,plain,
    ( r2_hidden(X0,k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,sK4))))) = iProver_top
    | r2_hidden(X0,k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13116,c_10856])).

cnf(c_14592,plain,
    ( r2_hidden(X0,k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_13239])).

cnf(c_14952,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10844,c_14592])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_222,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) != X1
    | k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_223,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_3907,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_3963,plain,
    ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3910,c_3907])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22346,c_14952,c_3963])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.73/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.50  
% 7.73/1.50  ------  iProver source info
% 7.73/1.50  
% 7.73/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.50  git: non_committed_changes: false
% 7.73/1.50  git: last_make_outside_of_git: false
% 7.73/1.50  
% 7.73/1.50  ------ 
% 7.73/1.50  ------ Parsing...
% 7.73/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  ------ Proving...
% 7.73/1.50  ------ Problem Properties 
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  clauses                                 20
% 7.73/1.50  conjectures                             2
% 7.73/1.50  EPR                                     2
% 7.73/1.50  Horn                                    16
% 7.73/1.50  unary                                   6
% 7.73/1.50  binary                                  5
% 7.73/1.50  lits                                    45
% 7.73/1.50  lits eq                                 9
% 7.73/1.50  fd_pure                                 0
% 7.73/1.50  fd_pseudo                               0
% 7.73/1.50  fd_cond                                 0
% 7.73/1.50  fd_pseudo_cond                          6
% 7.73/1.50  AC symbols                              0
% 7.73/1.50  
% 7.73/1.50  ------ Input Options Time Limit: Unbounded
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.73/1.50  Current options:
% 7.73/1.50  ------ 
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS status Theorem for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  fof(f2,axiom,(
% 7.73/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f11,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.73/1.50    inference(unused_predicate_definition_removal,[],[f2])).
% 7.73/1.50  
% 7.73/1.50  fof(f12,plain,(
% 7.73/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f11])).
% 7.73/1.50  
% 7.73/1.50  fof(f16,plain,(
% 7.73/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f17,plain,(
% 7.73/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 7.73/1.50  
% 7.73/1.50  fof(f32,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f17])).
% 7.73/1.50  
% 7.73/1.50  fof(f9,conjecture,(
% 7.73/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f10,negated_conjecture,(
% 7.73/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.73/1.50    inference(negated_conjecture,[],[f9])).
% 7.73/1.50  
% 7.73/1.50  fof(f15,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f10])).
% 7.73/1.50  
% 7.73/1.50  fof(f29,plain,(
% 7.73/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK4)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK4))) & v1_relat_1(sK4))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f28,plain,(
% 7.73/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK3,X1)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK3))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f30,plain,(
% 7.73/1.50    (~r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK4)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) & v1_relat_1(sK4)) & v1_relat_1(sK3)),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f29,f28])).
% 7.73/1.50  
% 7.73/1.50  fof(f52,plain,(
% 7.73/1.50    ~r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK4)),k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),
% 7.73/1.50    inference(cnf_transformation,[],[f30])).
% 7.73/1.50  
% 7.73/1.50  fof(f6,axiom,(
% 7.73/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f47,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f6])).
% 7.73/1.50  
% 7.73/1.50  fof(f62,plain,(
% 7.73/1.50    ~r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))))),
% 7.73/1.50    inference(definition_unfolding,[],[f52,f47,f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f1,axiom,(
% 7.73/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f31,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f1])).
% 7.73/1.50  
% 7.73/1.50  fof(f53,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.73/1.50    inference(definition_unfolding,[],[f31,f47,f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f51,plain,(
% 7.73/1.50    v1_relat_1(sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f30])).
% 7.73/1.50  
% 7.73/1.50  fof(f7,axiom,(
% 7.73/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f13,plain,(
% 7.73/1.50    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f7])).
% 7.73/1.50  
% 7.73/1.50  fof(f48,plain,(
% 7.73/1.50    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f13])).
% 7.73/1.50  
% 7.73/1.50  fof(f61,plain,(
% 7.73/1.50    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(definition_unfolding,[],[f48,f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f8,axiom,(
% 7.73/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f14,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f8])).
% 7.73/1.50  
% 7.73/1.50  fof(f49,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f14])).
% 7.73/1.50  
% 7.73/1.50  fof(f5,axiom,(
% 7.73/1.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f46,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.73/1.50    inference(cnf_transformation,[],[f5])).
% 7.73/1.50  
% 7.73/1.50  fof(f60,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 7.73/1.50    inference(definition_unfolding,[],[f46,f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f3,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f18,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(nnf_transformation,[],[f3])).
% 7.73/1.50  
% 7.73/1.50  fof(f19,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(flattening,[],[f18])).
% 7.73/1.50  
% 7.73/1.50  fof(f20,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(rectify,[],[f19])).
% 7.73/1.50  
% 7.73/1.50  fof(f21,plain,(
% 7.73/1.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f22,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 7.73/1.50  
% 7.73/1.50  fof(f36,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 7.73/1.50    inference(cnf_transformation,[],[f22])).
% 7.73/1.50  
% 7.73/1.50  fof(f63,plain,(
% 7.73/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 7.73/1.50    inference(equality_resolution,[],[f36])).
% 7.73/1.50  
% 7.73/1.50  fof(f50,plain,(
% 7.73/1.50    v1_relat_1(sK3)),
% 7.73/1.50    inference(cnf_transformation,[],[f30])).
% 7.73/1.50  
% 7.73/1.50  fof(f4,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f23,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(nnf_transformation,[],[f4])).
% 7.73/1.50  
% 7.73/1.50  fof(f24,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(flattening,[],[f23])).
% 7.73/1.50  
% 7.73/1.50  fof(f25,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(rectify,[],[f24])).
% 7.73/1.50  
% 7.73/1.50  fof(f26,plain,(
% 7.73/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f27,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 7.73/1.50  
% 7.73/1.50  fof(f42,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.73/1.50    inference(cnf_transformation,[],[f27])).
% 7.73/1.50  
% 7.73/1.50  fof(f57,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 7.73/1.50    inference(definition_unfolding,[],[f42,f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f66,plain,(
% 7.73/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f57])).
% 7.73/1.50  
% 7.73/1.50  fof(f33,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f17])).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2,plain,
% 7.73/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18,negated_conjecture,
% 7.73/1.50      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_215,plain,
% 7.73/1.50      ( r2_hidden(sK0(X0,X1),X0)
% 7.73/1.50      | k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) != X1
% 7.73/1.50      | k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != X0 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_216,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_215]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10844,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_0,plain,
% 7.73/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19,negated_conjecture,
% 7.73/1.50      ( v1_relat_1(sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10848,plain,
% 7.73/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_16,plain,
% 7.73/1.50      ( ~ v1_relat_1(X0)
% 7.73/1.50      | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10850,plain,
% 7.73/1.50      ( v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17,plain,
% 7.73/1.50      ( ~ v1_relat_1(X0)
% 7.73/1.50      | ~ v1_relat_1(X1)
% 7.73/1.50      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10849,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11026,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK4,X0))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10848,c_10849]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11125,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_relat_1(k2_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,X1))))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10850,c_11026]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11498,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k1_relat_1(k2_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10848,c_11125]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_15,plain,
% 7.73/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11513,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))) = k1_relat_1(sK4) ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11498,c_15]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11571,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) = k1_relat_1(sK4) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_0,c_11513]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6,plain,
% 7.73/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10856,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.50      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11673,plain,
% 7.73/1.50      ( r2_hidden(X0,k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,sK4)))) != iProver_top
% 7.73/1.50      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_11571,c_10856]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_22346,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK4)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10844,c_11673]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11053,plain,
% 7.73/1.50      ( v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_0,c_10850]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20,negated_conjecture,
% 7.73/1.50      ( v1_relat_1(sK3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10847,plain,
% 7.73/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11027,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK3,X0))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10847,c_10849]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11319,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1))))
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_11053,c_11027]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13116,plain,
% 7.73/1.50      ( k2_xboole_0(k1_relat_1(sK3),k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) = k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK4)))) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10848,c_11319]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13239,plain,
% 7.73/1.50      ( r2_hidden(X0,k1_relat_1(k2_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,sK4))))) = iProver_top
% 7.73/1.50      | r2_hidden(X0,k1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,sK4)))) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_13116,c_10856]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14592,plain,
% 7.73/1.50      ( r2_hidden(X0,k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) != iProver_top
% 7.73/1.50      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_15,c_13239]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14952,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK3)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10844,c_14592]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12,plain,
% 7.73/1.50      ( ~ r2_hidden(X0,X1)
% 7.73/1.50      | ~ r2_hidden(X0,X2)
% 7.73/1.50      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3910,plain,
% 7.73/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.50      | r2_hidden(X0,X2) != iProver_top
% 7.73/1.50      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1,plain,
% 7.73/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_222,plain,
% 7.73/1.50      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.73/1.50      | k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) != X1
% 7.73/1.50      | k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != X0 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_223,plain,
% 7.73/1.50      ( ~ r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_222]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3907,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3963,plain,
% 7.73/1.50      ( r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK4)) != iProver_top
% 7.73/1.50      | r2_hidden(sK0(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k1_relat_1(sK3)) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3910,c_3907]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(contradiction,plain,
% 7.73/1.50      ( $false ),
% 7.73/1.50      inference(minisat,[status(thm)],[c_22346,c_14952,c_3963]) ).
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  ------                               Statistics
% 7.73/1.50  
% 7.73/1.50  ------ Selected
% 7.73/1.50  
% 7.73/1.50  total_time:                             0.77
% 7.73/1.50  
%------------------------------------------------------------------------------
