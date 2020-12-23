%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:33 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 268 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 922 expanded)
%              Number of equality atoms :   49 ( 284 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f167])).

fof(f167,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f166,f165])).

fof(f165,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f164,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f164,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
    | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != k2_tarski(sK0,X0)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))) ) ),
    inference(superposition,[],[f76,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f40,f38,f36,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1)))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))) ) ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f58,f60,f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f38,f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f49,f38,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f72,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X0)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X0),X0) ) ),
    inference(superposition,[],[f63,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f34,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f166,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != k2_tarski(sK0,X0)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))) ) ),
    inference(superposition,[],[f87,f62])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1)))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))) ) ),
    inference(subsumption_resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1)))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))) ) ),
    inference(superposition,[],[f74,f66])).

fof(f74,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X2)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),k2_tarski(sK0,sK0))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),X2) ) ),
    inference(superposition,[],[f63,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f244,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f94,f165,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f89,f62])).

fof(f89,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f62,f82])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1)))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f79,f70])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1)))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))) ) ),
    inference(superposition,[],[f73,f66])).

fof(f73,plain,(
    ! [X1] :
      ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X1)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X1),k2_tarski(sK0,sK0))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X1),X1) ) ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (31454)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (31470)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (31462)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (31453)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (31459)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (31470)Refutation not found, incomplete strategy% (31470)------------------------------
% 0.22/0.53  % (31470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31459)Refutation not found, incomplete strategy% (31459)------------------------------
% 0.22/0.53  % (31459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31459)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31459)Memory used [KB]: 10618
% 0.22/0.53  % (31459)Time elapsed: 0.107 s
% 0.22/0.53  % (31459)------------------------------
% 0.22/0.53  % (31459)------------------------------
% 0.22/0.53  % (31470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31470)Memory used [KB]: 10618
% 0.22/0.53  % (31470)Time elapsed: 0.108 s
% 0.22/0.53  % (31470)------------------------------
% 0.22/0.53  % (31470)------------------------------
% 0.22/0.54  % (31463)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (31448)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (31448)Refutation not found, incomplete strategy% (31448)------------------------------
% 0.22/0.54  % (31448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31448)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31448)Memory used [KB]: 1663
% 0.22/0.54  % (31448)Time elapsed: 0.116 s
% 0.22/0.54  % (31448)------------------------------
% 0.22/0.54  % (31448)------------------------------
% 0.22/0.54  % (31455)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (31450)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (31471)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  % (31477)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (31472)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.54  % (31471)Refutation not found, incomplete strategy% (31471)------------------------------
% 1.39/0.54  % (31471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (31471)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (31471)Memory used [KB]: 1663
% 1.39/0.54  % (31471)Time elapsed: 0.089 s
% 1.39/0.54  % (31471)------------------------------
% 1.39/0.54  % (31471)------------------------------
% 1.39/0.54  % (31450)Refutation not found, incomplete strategy% (31450)------------------------------
% 1.39/0.54  % (31450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (31451)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.55  % (31449)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.55  % (31466)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (31450)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (31450)Memory used [KB]: 10618
% 1.39/0.55  % (31450)Time elapsed: 0.125 s
% 1.39/0.55  % (31450)------------------------------
% 1.39/0.55  % (31450)------------------------------
% 1.39/0.55  % (31458)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (31464)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.55  % (31456)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (31465)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.55  % (31475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (31467)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (31457)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (31474)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.56  % (31461)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.56  % (31469)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.56  % (31473)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.56  % (31469)Refutation not found, incomplete strategy% (31469)------------------------------
% 1.39/0.56  % (31469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (31469)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (31469)Memory used [KB]: 1663
% 1.39/0.56  % (31469)Time elapsed: 0.142 s
% 1.39/0.56  % (31469)------------------------------
% 1.39/0.56  % (31469)------------------------------
% 1.39/0.56  % (31456)Refutation not found, incomplete strategy% (31456)------------------------------
% 1.39/0.56  % (31456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (31456)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (31456)Memory used [KB]: 10618
% 1.39/0.56  % (31456)Time elapsed: 0.140 s
% 1.39/0.56  % (31456)------------------------------
% 1.39/0.56  % (31456)------------------------------
% 1.57/0.56  % (31465)Refutation not found, incomplete strategy% (31465)------------------------------
% 1.57/0.56  % (31465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (31473)Refutation not found, incomplete strategy% (31473)------------------------------
% 1.57/0.56  % (31473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (31458)Refutation not found, incomplete strategy% (31458)------------------------------
% 1.57/0.56  % (31458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (31458)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (31458)Memory used [KB]: 10618
% 1.57/0.56  % (31458)Time elapsed: 0.151 s
% 1.57/0.56  % (31458)------------------------------
% 1.57/0.56  % (31458)------------------------------
% 1.57/0.56  % (31457)Refutation not found, incomplete strategy% (31457)------------------------------
% 1.57/0.56  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (31457)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (31457)Memory used [KB]: 10618
% 1.57/0.56  % (31457)Time elapsed: 0.151 s
% 1.57/0.56  % (31457)------------------------------
% 1.57/0.56  % (31457)------------------------------
% 1.57/0.56  % (31465)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (31465)Memory used [KB]: 10618
% 1.57/0.56  % (31465)Time elapsed: 0.152 s
% 1.57/0.56  % (31465)------------------------------
% 1.57/0.56  % (31465)------------------------------
% 1.57/0.57  % (31476)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.57  % (31473)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (31473)Memory used [KB]: 6268
% 1.57/0.57  % (31473)Time elapsed: 0.149 s
% 1.57/0.57  % (31473)------------------------------
% 1.57/0.57  % (31473)------------------------------
% 1.57/0.57  % (31452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.57/0.58  % (31468)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.58  % (31452)Refutation not found, incomplete strategy% (31452)------------------------------
% 1.57/0.58  % (31452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (31452)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (31452)Memory used [KB]: 6140
% 1.57/0.58  % (31452)Time elapsed: 0.132 s
% 1.57/0.58  % (31452)------------------------------
% 1.57/0.58  % (31452)------------------------------
% 1.57/0.58  % (31460)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.59  % (31468)Refutation not found, incomplete strategy% (31468)------------------------------
% 1.57/0.59  % (31468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (31468)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (31468)Memory used [KB]: 10618
% 1.57/0.59  % (31468)Time elapsed: 0.145 s
% 1.57/0.59  % (31468)------------------------------
% 1.57/0.59  % (31468)------------------------------
% 1.57/0.61  % (31474)Refutation found. Thanks to Tanya!
% 1.57/0.61  % SZS status Theorem for theBenchmark
% 1.57/0.61  % SZS output start Proof for theBenchmark
% 1.57/0.61  fof(f252,plain,(
% 1.57/0.61    $false),
% 1.57/0.61    inference(subsumption_resolution,[],[f244,f167])).
% 1.57/0.61  fof(f167,plain,(
% 1.57/0.61    ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.57/0.61    inference(subsumption_resolution,[],[f166,f165])).
% 1.57/0.61  fof(f165,plain,(
% 1.57/0.61    r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f164,f71])).
% 1.57/0.61  fof(f71,plain,(
% 1.57/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.57/0.61    inference(equality_resolution,[],[f51])).
% 1.57/0.61  fof(f51,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f33,plain,(
% 1.57/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.57/0.61  fof(f32,plain,(
% 1.57/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.57/0.61    introduced(choice_axiom,[])).
% 1.57/0.61  fof(f31,plain,(
% 1.57/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.61    inference(rectify,[],[f30])).
% 1.57/0.61  fof(f30,plain,(
% 1.57/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.61    inference(flattening,[],[f29])).
% 1.57/0.61  fof(f29,plain,(
% 1.57/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.61    inference(nnf_transformation,[],[f3])).
% 1.57/0.61  fof(f3,axiom,(
% 1.57/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.57/0.61  fof(f164,plain,(
% 1.57/0.61    r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.57/0.61    inference(equality_resolution,[],[f131])).
% 1.57/0.61  fof(f131,plain,(
% 1.57/0.61    ( ! [X0] : (k2_tarski(sK0,sK1) != k2_tarski(sK0,X0) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(superposition,[],[f76,f62])).
% 1.57/0.61  fof(f62,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f40,f38,f36,f36])).
% 1.57/0.61  fof(f36,plain,(
% 1.57/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f15])).
% 1.57/0.61  fof(f15,axiom,(
% 1.57/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.61  fof(f38,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f10])).
% 1.57/0.61  fof(f10,axiom,(
% 1.57/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.57/0.61  fof(f40,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f12])).
% 1.57/0.61  fof(f12,axiom,(
% 1.57/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.57/0.61  fof(f76,plain,(
% 1.57/0.61    ( ! [X2,X3,X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1))) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(superposition,[],[f72,f66])).
% 1.57/0.61  fof(f66,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f58,f60,f38])).
% 1.57/0.61  fof(f60,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0)))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f57,f38,f36,f59])).
% 1.57/0.61  fof(f59,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.57/0.61    inference(definition_unfolding,[],[f49,f38,f36])).
% 1.57/0.61  fof(f49,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f13])).
% 1.57/0.61  fof(f13,axiom,(
% 1.57/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.57/0.61  fof(f57,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f14])).
% 1.57/0.61  fof(f14,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 1.57/0.61  fof(f58,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f11])).
% 1.57/0.61  fof(f11,axiom,(
% 1.57/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.57/0.61  fof(f72,plain,(
% 1.57/0.61    ( ! [X0] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X0) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X0),X0)) )),
% 1.57/0.61    inference(superposition,[],[f63,f54])).
% 1.57/0.61  fof(f54,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f63,plain,(
% 1.57/0.61    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.57/0.61    inference(definition_unfolding,[],[f34,f59])).
% 1.57/0.61  fof(f34,plain,(
% 1.57/0.61    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.57/0.61    inference(cnf_transformation,[],[f22])).
% 1.57/0.61  fof(f22,plain,(
% 1.57/0.61    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.57/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).
% 1.57/0.61  fof(f21,plain,(
% 1.57/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.57/0.61    introduced(choice_axiom,[])).
% 1.57/0.61  fof(f18,plain,(
% 1.57/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.57/0.61    inference(ennf_transformation,[],[f17])).
% 1.57/0.61  fof(f17,negated_conjecture,(
% 1.57/0.61    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.57/0.61    inference(negated_conjecture,[],[f16])).
% 1.57/0.61  fof(f16,conjecture,(
% 1.57/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.61  fof(f166,plain,(
% 1.57/0.61    ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.57/0.61    inference(equality_resolution,[],[f135])).
% 1.57/0.61  fof(f135,plain,(
% 1.57/0.61    ( ! [X0] : (k2_tarski(sK0,sK1) != k2_tarski(sK0,X0) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,X0),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(superposition,[],[f87,f62])).
% 1.57/0.61  fof(f87,plain,(
% 1.57/0.61    ( ! [X2,X3,X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1))) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f84,f70])).
% 1.57/0.61  fof(f70,plain,(
% 1.57/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.57/0.61    inference(equality_resolution,[],[f52])).
% 1.57/0.61  fof(f52,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f84,plain,(
% 1.57/0.61    ( ! [X2,X3,X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1))) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(superposition,[],[f74,f66])).
% 1.57/0.61  fof(f74,plain,(
% 1.57/0.61    ( ! [X2] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X2) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),k2_tarski(sK0,sK0)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X2),X2)) )),
% 1.57/0.61    inference(superposition,[],[f63,f56])).
% 1.57/0.61  fof(f56,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f244,plain,(
% 1.57/0.61    r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.57/0.61    inference(unit_resulting_resolution,[],[f94,f165,f69])).
% 1.57/0.61  fof(f69,plain,(
% 1.57/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.57/0.61    inference(equality_resolution,[],[f53])).
% 1.57/0.61  fof(f53,plain,(
% 1.57/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f94,plain,(
% 1.57/0.61    ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))),
% 1.57/0.61    inference(forward_demodulation,[],[f89,f62])).
% 1.57/0.61  fof(f89,plain,(
% 1.57/0.61    ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))),
% 1.57/0.61    inference(unit_resulting_resolution,[],[f62,f82])).
% 1.57/0.61  fof(f82,plain,(
% 1.57/0.61    ( ! [X2,X3,X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1))) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f79,f70])).
% 1.57/0.61  fof(f79,plain,(
% 1.57/0.61    ( ! [X2,X3,X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(sK0,X1))) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(sK0,sK0)))) )),
% 1.57/0.61    inference(superposition,[],[f73,f66])).
% 1.57/0.61  fof(f73,plain,(
% 1.57/0.61    ( ! [X1] : (k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),X1) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X1),k2_tarski(sK0,sK0)) | r2_hidden(sK3(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0),X1),X1)) )),
% 1.57/0.61    inference(superposition,[],[f63,f55])).
% 1.57/0.61  fof(f55,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  % SZS output end Proof for theBenchmark
% 1.57/0.61  % (31474)------------------------------
% 1.57/0.61  % (31474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (31474)Termination reason: Refutation
% 1.57/0.61  
% 1.57/0.61  % (31474)Memory used [KB]: 11001
% 1.57/0.61  % (31474)Time elapsed: 0.183 s
% 1.57/0.61  % (31474)------------------------------
% 1.57/0.61  % (31474)------------------------------
% 1.57/0.62  % (31447)Success in time 0.241 s
%------------------------------------------------------------------------------
