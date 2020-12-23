%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:21 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   20
%              Number of atoms          :   93 ( 174 expanded)
%              Number of equality atoms :   66 ( 130 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f278,f67])).

% (30536)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f67,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f66])).

% (30560)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f66,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f278,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))))) ),
    inference(forward_demodulation,[],[f277,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f277,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))) ),
    inference(forward_demodulation,[],[f276,f38])).

fof(f276,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f265,f38])).

fof(f265,plain,(
    ~ r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))) ),
    inference(unit_resulting_resolution,[],[f245,f68])).

fof(f68,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f245,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f244,f38])).

fof(f244,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f243,f38])).

fof(f243,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f242,f38])).

fof(f242,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f241,f38])).

fof(f241,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f240,f38])).

fof(f240,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))) ),
    inference(forward_demodulation,[],[f239,f38])).

fof(f239,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))) ),
    inference(forward_demodulation,[],[f238,f38])).

fof(f238,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f237,f38])).

fof(f237,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f57,f38])).

fof(f57,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f29,f54,f31,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X4),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f51,f53,f53])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f29,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.35  % Computer   : n018.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 17:02:57 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.22/0.50  % (30535)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (30534)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.15/0.51  % (30544)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.15/0.52  % (30546)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.15/0.52  % (30535)Refutation found. Thanks to Tanya!
% 1.15/0.52  % SZS status Theorem for theBenchmark
% 1.15/0.52  % (30533)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.15/0.52  % (30541)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.15/0.52  % (30546)Refutation not found, incomplete strategy% (30546)------------------------------
% 1.15/0.52  % (30546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (30546)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.52  
% 1.15/0.52  % (30546)Memory used [KB]: 1663
% 1.15/0.52  % (30546)Time elapsed: 0.114 s
% 1.15/0.52  % (30546)------------------------------
% 1.15/0.52  % (30546)------------------------------
% 1.15/0.52  % SZS output start Proof for theBenchmark
% 1.15/0.52  fof(f279,plain,(
% 1.15/0.52    $false),
% 1.15/0.52    inference(subsumption_resolution,[],[f278,f67])).
% 1.15/0.52  % (30536)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.15/0.52  fof(f67,plain,(
% 1.15/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.15/0.52    inference(equality_resolution,[],[f66])).
% 1.15/0.52  % (30560)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.15/0.52  fof(f66,plain,(
% 1.15/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.15/0.52    inference(equality_resolution,[],[f34])).
% 1.15/0.52  fof(f34,plain,(
% 1.15/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.15/0.52    inference(cnf_transformation,[],[f23])).
% 1.15/0.52  fof(f23,plain,(
% 1.15/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f22])).
% 1.15/0.52  fof(f22,plain,(
% 1.15/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 1.15/0.52    introduced(choice_axiom,[])).
% 1.15/0.52  fof(f21,plain,(
% 1.15/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.52    inference(rectify,[],[f20])).
% 1.15/0.52  fof(f20,plain,(
% 1.15/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.52    inference(nnf_transformation,[],[f6])).
% 1.15/0.52  fof(f6,axiom,(
% 1.15/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.15/0.52  fof(f278,plain,(
% 1.15/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f277,f38])).
% 1.15/0.52  fof(f38,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f3])).
% 1.15/0.52  fof(f3,axiom,(
% 1.15/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.15/0.52  fof(f277,plain,(
% 1.15/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f276,f38])).
% 1.15/0.52  fof(f276,plain,(
% 1.15/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f265,f38])).
% 1.15/0.52  fof(f265,plain,(
% 1.15/0.52    ~r2_hidden(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),k1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f245,f68])).
% 1.15/0.52  fof(f68,plain,(
% 1.15/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.15/0.52    inference(equality_resolution,[],[f33])).
% 1.15/0.52  fof(f33,plain,(
% 1.15/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.15/0.52    inference(cnf_transformation,[],[f23])).
% 1.15/0.52  fof(f245,plain,(
% 1.15/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 1.15/0.52    inference(forward_demodulation,[],[f244,f38])).
% 1.15/0.52  fof(f244,plain,(
% 1.15/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 1.15/0.52    inference(forward_demodulation,[],[f243,f38])).
% 1.15/0.52  fof(f243,plain,(
% 1.15/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 1.15/0.52    inference(forward_demodulation,[],[f242,f38])).
% 1.15/0.52  fof(f242,plain,(
% 1.15/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 1.15/0.52    inference(forward_demodulation,[],[f241,f38])).
% 1.15/0.52  fof(f241,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f240,f38])).
% 1.15/0.52  fof(f240,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f239,f38])).
% 1.15/0.52  fof(f239,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))),
% 1.15/0.52    inference(forward_demodulation,[],[f238,f38])).
% 1.15/0.52  fof(f238,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 1.15/0.52    inference(forward_demodulation,[],[f237,f38])).
% 1.15/0.52  fof(f237,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))))),
% 1.15/0.52    inference(forward_demodulation,[],[f57,f38])).
% 1.15/0.52  fof(f57,plain,(
% 1.15/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k1_tarski(sK6)),k1_tarski(sK7)))),
% 1.15/0.52    inference(definition_unfolding,[],[f29,f54,f31,f56])).
% 1.15/0.52  fof(f56,plain,(
% 1.15/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5))) )),
% 1.15/0.52    inference(definition_unfolding,[],[f50,f55])).
% 1.15/0.52  fof(f55,plain,(
% 1.15/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))) )),
% 1.15/0.52    inference(definition_unfolding,[],[f49,f53])).
% 1.15/0.52  fof(f53,plain,(
% 1.15/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3))) )),
% 1.15/0.52    inference(definition_unfolding,[],[f39,f52])).
% 1.15/0.52  fof(f52,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 1.15/0.52    inference(definition_unfolding,[],[f37,f31])).
% 1.15/0.52  fof(f37,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f9])).
% 1.15/0.52  fof(f9,axiom,(
% 1.15/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 1.15/0.52  fof(f39,plain,(
% 1.15/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f10])).
% 1.15/0.52  fof(f10,axiom,(
% 1.15/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.15/0.52  fof(f49,plain,(
% 1.15/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f11,axiom,(
% 1.15/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 1.15/0.52  fof(f50,plain,(
% 1.15/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f12])).
% 1.15/0.52  fof(f12,axiom,(
% 1.15/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 1.15/0.52  fof(f31,plain,(
% 1.15/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f8])).
% 1.15/0.52  fof(f8,axiom,(
% 1.15/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.15/0.52  fof(f54,plain,(
% 1.15/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X4),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7)))) )),
% 1.15/0.52    inference(definition_unfolding,[],[f51,f53,f53])).
% 1.15/0.52  fof(f51,plain,(
% 1.15/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f7])).
% 1.15/0.52  fof(f7,axiom,(
% 1.15/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.15/0.52  fof(f29,plain,(
% 1.15/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.15/0.52    inference(cnf_transformation,[],[f19])).
% 1.15/0.52  fof(f19,plain,(
% 1.15/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.15/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f18])).
% 1.15/0.52  fof(f18,plain,(
% 1.15/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.15/0.52    introduced(choice_axiom,[])).
% 1.15/0.52  fof(f16,plain,(
% 1.15/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 1.15/0.52    inference(ennf_transformation,[],[f14])).
% 1.15/0.52  fof(f14,negated_conjecture,(
% 1.15/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 1.15/0.52    inference(negated_conjecture,[],[f13])).
% 1.15/0.52  fof(f13,conjecture,(
% 1.15/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 1.15/0.52  % SZS output end Proof for theBenchmark
% 1.15/0.52  % (30535)------------------------------
% 1.15/0.52  % (30535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (30535)Termination reason: Refutation
% 1.15/0.52  
% 1.15/0.52  % (30535)Memory used [KB]: 1918
% 1.15/0.52  % (30535)Time elapsed: 0.105 s
% 1.15/0.52  % (30535)------------------------------
% 1.15/0.52  % (30535)------------------------------
% 1.15/0.53  % (30528)Success in time 0.157 s
%------------------------------------------------------------------------------
