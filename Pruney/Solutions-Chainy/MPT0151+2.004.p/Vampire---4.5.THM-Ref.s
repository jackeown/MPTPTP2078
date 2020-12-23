%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:27 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  98 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   21
%              Number of atoms          :   94 ( 177 expanded)
%              Number of equality atoms :   66 ( 132 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

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

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f56,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))))) ),
    inference(forward_demodulation,[],[f55,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f55,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))) ),
    inference(forward_demodulation,[],[f54,f26])).

fof(f54,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f53,f26])).

fof(f53,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))) ),
    inference(forward_demodulation,[],[f51,f26])).

fof(f51,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))) ),
    inference(unit_resulting_resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f48,f26])).

fof(f48,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f47,f26])).

fof(f47,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f46,f26])).

fof(f46,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f45,f26])).

fof(f45,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f44,f26])).

fof(f44,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))) ),
    inference(forward_demodulation,[],[f43,f26])).

fof(f43,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))) ),
    inference(forward_demodulation,[],[f42,f26])).

fof(f42,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f41,f26])).

fof(f41,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f37,f26])).

fof(f37,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f19,f36,f35,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f31,f34,f32])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (8080)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.52  % (8073)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.52  % (8080)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(subsumption_resolution,[],[f56,f39])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.23/0.52    inference(equality_resolution,[],[f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.23/0.52    inference(equality_resolution,[],[f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.52    inference(rectify,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.52    inference(nnf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.52  fof(f56,plain,(
% 0.23/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f55,f26])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f54,f26])).
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f53,f26])).
% 0.23/0.52  fof(f53,plain,(
% 0.23/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f51,f26])).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f49,f40])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.23/0.52    inference(equality_resolution,[],[f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.23/0.52    inference(forward_demodulation,[],[f48,f26])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.23/0.52    inference(forward_demodulation,[],[f47,f26])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.23/0.52    inference(forward_demodulation,[],[f46,f26])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f45,f26])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f44,f26])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f43,f26])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))),
% 0.23/0.52    inference(forward_demodulation,[],[f42,f26])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 0.23/0.52    inference(forward_demodulation,[],[f41,f26])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.23/0.52    inference(forward_demodulation,[],[f37,f26])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))),
% 0.23/0.52    inference(definition_unfolding,[],[f19,f36,f35,f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f30,f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f29,f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f27,f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f25,f20])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f31,f34,f32])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.23/0.52    inference(cnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.23/0.52    inference(ennf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.23/0.52    inference(negated_conjecture,[],[f10])).
% 0.23/0.52  fof(f10,conjecture,(
% 0.23/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (8080)------------------------------
% 0.23/0.52  % (8080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (8080)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (8080)Memory used [KB]: 6140
% 0.23/0.52  % (8080)Time elapsed: 0.094 s
% 0.23/0.52  % (8080)------------------------------
% 0.23/0.52  % (8080)------------------------------
% 0.23/0.52  % (8068)Success in time 0.15 s
%------------------------------------------------------------------------------
