%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:58 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 252 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  204 ( 662 expanded)
%              Number of equality atoms :   99 ( 307 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f306])).

fof(f306,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(forward_demodulation,[],[f302,f67])).

fof(f67,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f302,plain,(
    ! [X14,X15] : k3_xboole_0(X14,k1_setfam_1(k2_tarski(X15,X15))) = k1_setfam_1(k2_tarski(X14,X15)) ),
    inference(superposition,[],[f199,f287])).

fof(f287,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X1,X1,X1) ),
    inference(forward_demodulation,[],[f274,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f274,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X1,X1,X1) ),
    inference(superposition,[],[f263,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
    inference(superposition,[],[f66,f65])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f51,f42,f40,f50])).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f263,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f223,f65])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X1,X1,X2),k2_tarski(X3,X3))) ),
    inference(superposition,[],[f71,f66])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4))) = k3_tarski(k2_tarski(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X4))) ),
    inference(definition_unfolding,[],[f63,f64,f42,f40])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f62,f42,f40])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f199,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k2_enumset1(X0,X1,X1,X2)) = k3_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(forward_demodulation,[],[f198,f67])).

fof(f198,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2)) ),
    inference(subsumption_resolution,[],[f197,f128])).

fof(f128,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X1,X0) ),
    inference(subsumption_resolution,[],[f124,f114])).

fof(f114,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f108,f72])).

fof(f72,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f108,plain,(
    ! [X6,X4,X5] :
      ( ~ sP0(X4,X5,X6,X6)
      | r2_hidden(X4,k2_tarski(X6,X5)) ) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,(
    ! [X0,X1] : sP1(X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f75,f65])).

fof(f75,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

% (1617)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X0))
      | k1_xboole_0 != k2_tarski(X1,X0) ) ),
    inference(resolution,[],[f118,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_tarski(X1,X2))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f114,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2))
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(subsumption_resolution,[],[f196,f128])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2))
      | k1_xboole_0 = k2_tarski(X1,X2)
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(superposition,[],[f68,f129])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f38,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (1603)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.48  % (1610)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (1603)Refutation not found, incomplete strategy% (1603)------------------------------
% 0.21/0.50  % (1603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1603)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1603)Memory used [KB]: 10618
% 0.21/0.50  % (1603)Time elapsed: 0.077 s
% 0.21/0.50  % (1603)------------------------------
% 0.21/0.50  % (1603)------------------------------
% 0.21/0.50  % (1600)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (1623)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (1611)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (1607)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (1598)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1597)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1611)Refutation not found, incomplete strategy% (1611)------------------------------
% 0.21/0.52  % (1611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1596)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (1620)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (1611)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1611)Memory used [KB]: 10618
% 0.21/0.53  % (1611)Time elapsed: 0.113 s
% 0.21/0.53  % (1611)------------------------------
% 0.21/0.53  % (1611)------------------------------
% 0.21/0.53  % (1599)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1596)Refutation not found, incomplete strategy% (1596)------------------------------
% 0.21/0.53  % (1596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1596)Memory used [KB]: 10618
% 0.21/0.53  % (1596)Time elapsed: 0.124 s
% 0.21/0.53  % (1596)------------------------------
% 0.21/0.53  % (1596)------------------------------
% 0.21/0.53  % (1598)Refutation not found, incomplete strategy% (1598)------------------------------
% 0.21/0.53  % (1598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1598)Memory used [KB]: 6268
% 0.21/0.53  % (1598)Time elapsed: 0.125 s
% 0.21/0.53  % (1598)------------------------------
% 0.21/0.53  % (1598)------------------------------
% 1.25/0.54  % (1621)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.54  % (1619)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.54  % (1619)Refutation not found, incomplete strategy% (1619)------------------------------
% 1.25/0.54  % (1619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (1619)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (1619)Memory used [KB]: 6268
% 1.25/0.54  % (1619)Time elapsed: 0.128 s
% 1.25/0.54  % (1619)------------------------------
% 1.25/0.54  % (1619)------------------------------
% 1.25/0.54  % (1606)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (1613)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.54  % (1612)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.54  % (1601)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.54  % (1604)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.55  % (1595)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.55  % (1622)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.55  % (1604)Refutation not found, incomplete strategy% (1604)------------------------------
% 1.25/0.55  % (1604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (1605)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.55  % (1604)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (1604)Memory used [KB]: 10618
% 1.51/0.55  % (1604)Time elapsed: 0.140 s
% 1.51/0.55  % (1604)------------------------------
% 1.51/0.55  % (1604)------------------------------
% 1.51/0.55  % (1605)Refutation not found, incomplete strategy% (1605)------------------------------
% 1.51/0.55  % (1605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (1605)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (1605)Memory used [KB]: 10618
% 1.51/0.55  % (1605)Time elapsed: 0.147 s
% 1.51/0.55  % (1605)------------------------------
% 1.51/0.55  % (1605)------------------------------
% 1.51/0.55  % (1594)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.55  % (1594)Refutation not found, incomplete strategy% (1594)------------------------------
% 1.51/0.55  % (1594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (1594)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.56  % (1594)Memory used [KB]: 1663
% 1.51/0.56  % (1594)Time elapsed: 0.145 s
% 1.51/0.56  % (1594)------------------------------
% 1.51/0.56  % (1594)------------------------------
% 1.51/0.56  % (1614)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.56  % (1615)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.56  % (1614)Refutation not found, incomplete strategy% (1614)------------------------------
% 1.51/0.56  % (1614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (1614)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (1614)Memory used [KB]: 10746
% 1.51/0.56  % (1614)Time elapsed: 0.146 s
% 1.51/0.56  % (1614)------------------------------
% 1.51/0.56  % (1614)------------------------------
% 1.51/0.56  % (1615)Refutation not found, incomplete strategy% (1615)------------------------------
% 1.51/0.56  % (1615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (1615)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (1615)Memory used [KB]: 1663
% 1.51/0.56  % (1615)Time elapsed: 0.137 s
% 1.51/0.56  % (1615)------------------------------
% 1.51/0.56  % (1615)------------------------------
% 1.51/0.56  % (1616)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.56  % (1616)Refutation not found, incomplete strategy% (1616)------------------------------
% 1.51/0.56  % (1616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (1616)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (1616)Memory used [KB]: 10746
% 1.51/0.56  % (1616)Time elapsed: 0.152 s
% 1.51/0.56  % (1616)------------------------------
% 1.51/0.56  % (1616)------------------------------
% 1.51/0.56  % (1621)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f308,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(subsumption_resolution,[],[f38,f306])).
% 1.51/0.56  fof(f306,plain,(
% 1.51/0.56    ( ! [X14,X15] : (k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f302,f67])).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.51/0.56    inference(definition_unfolding,[],[f39,f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.51/0.56  fof(f302,plain,(
% 1.51/0.56    ( ! [X14,X15] : (k3_xboole_0(X14,k1_setfam_1(k2_tarski(X15,X15))) = k1_setfam_1(k2_tarski(X14,X15))) )),
% 1.51/0.56    inference(superposition,[],[f199,f287])).
% 1.51/0.56  fof(f287,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X1,X1,X1)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f274,f65])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.51/0.56    inference(definition_unfolding,[],[f43,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.56  fof(f274,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X1,X1,X1)) )),
% 1.51/0.56    inference(superposition,[],[f263,f129])).
% 1.51/0.56  fof(f129,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X0,X1)))) )),
% 1.51/0.56    inference(superposition,[],[f66,f65])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X1,X2,X3)))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f51,f42,f40,f50])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 1.51/0.56  fof(f263,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 1.51/0.56    inference(superposition,[],[f223,f65])).
% 1.51/0.56  fof(f223,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X1,X1,X2),k2_tarski(X3,X3)))) )),
% 1.51/0.56    inference(superposition,[],[f71,f66])).
% 1.51/0.56  fof(f71,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4))) = k3_tarski(k2_tarski(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X4)))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f63,f64,f42,f40])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4)))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f62,f42,f40])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 1.51/0.56  fof(f199,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X1,X1,X2)) = k3_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.51/0.56    inference(forward_demodulation,[],[f198,f67])).
% 1.51/0.56  fof(f198,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f197,f128])).
% 1.51/0.56  fof(f128,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X1,X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f124,f114])).
% 1.51/0.56  fof(f114,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.51/0.56    inference(resolution,[],[f108,f72])).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 1.51/0.56    inference(equality_resolution,[],[f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 1.51/0.56    inference(rectify,[],[f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 1.51/0.56    inference(flattening,[],[f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 1.51/0.56    inference(nnf_transformation,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.51/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.51/0.56  fof(f108,plain,(
% 1.51/0.56    ( ! [X6,X4,X5] : (~sP0(X4,X5,X6,X6) | r2_hidden(X4,k2_tarski(X6,X5))) )),
% 1.51/0.56    inference(resolution,[],[f53,f83])).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    ( ! [X0,X1] : (sP1(X0,X0,X1,k2_tarski(X0,X1))) )),
% 1.51/0.56    inference(superposition,[],[f75,f65])).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k2_enumset1(X0,X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.51/0.56    inference(definition_unfolding,[],[f60,f50])).
% 1.51/0.56  fof(f60,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.51/0.56    inference(nnf_transformation,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 1.51/0.56    inference(definition_folding,[],[f21,f23,f22])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 1.51/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.51/0.56    inference(ennf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.51/0.56  % (1617)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.51/0.56    inference(rectify,[],[f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.51/0.56    inference(nnf_transformation,[],[f23])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X0)) | k1_xboole_0 != k2_tarski(X1,X0)) )),
% 1.51/0.56    inference(resolution,[],[f118,f78])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.51/0.56    inference(superposition,[],[f48,f41])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f16])).
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.51/0.56    inference(rectify,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.51/0.56  fof(f48,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.51/0.56  fof(f118,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_tarski(X1,X2)) | ~r2_hidden(X2,X0)) )),
% 1.51/0.56    inference(resolution,[],[f114,f46])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(rectify,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.51/0.56  fof(f197,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2)) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f196,f128])).
% 1.51/0.56  fof(f196,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k1_setfam_1(k2_tarski(X0,X0)),k1_setfam_1(k2_tarski(X1,X2))) = k1_setfam_1(k2_enumset1(X0,X1,X1,X2)) | k1_xboole_0 = k2_tarski(X1,X2) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.51/0.56    inference(superposition,[],[f68,f129])).
% 1.51/0.56  fof(f68,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.56    inference(definition_unfolding,[],[f49,f42])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,axiom,(
% 1.51/0.56    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.51/0.56    inference(cnf_transformation,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.51/0.56    inference(negated_conjecture,[],[f14])).
% 1.51/0.56  fof(f14,conjecture,(
% 1.51/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (1621)------------------------------
% 1.51/0.56  % (1621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (1621)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (1621)Memory used [KB]: 6396
% 1.51/0.56  % (1621)Time elapsed: 0.137 s
% 1.51/0.56  % (1621)------------------------------
% 1.51/0.56  % (1621)------------------------------
% 1.51/0.56  % (1617)Refutation not found, incomplete strategy% (1617)------------------------------
% 1.51/0.56  % (1617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (1617)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (1617)Memory used [KB]: 1663
% 1.51/0.56  % (1617)Time elapsed: 0.150 s
% 1.51/0.56  % (1617)------------------------------
% 1.51/0.56  % (1617)------------------------------
% 1.51/0.56  % (1593)Success in time 0.194 s
%------------------------------------------------------------------------------
