%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:17 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  41 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 103 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f11,f25,f31,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f16,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f31,plain,(
    ~ sQ2_eqProxy(sK0,sK1) ),
    inference(resolution,[],[f27,f17])).

fof(f17,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( r2_xboole_0(sK1,X0)
      | ~ sQ2_eqProxy(sK0,X0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(sK1,X1)
      | ~ sQ2_eqProxy(sK0,X0)
      | r2_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f20,f12])).

fof(f12,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( r2_xboole_0(sK1,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_xboole_0(X0,X2)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ sQ2_eqProxy(X0,X1)
      | r2_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f18])).

fof(f25,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f13,f12])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
