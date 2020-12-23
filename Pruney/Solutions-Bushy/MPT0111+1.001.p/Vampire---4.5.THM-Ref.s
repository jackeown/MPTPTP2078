%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 152 expanded)
%              Number of leaves         :    4 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :   84 ( 466 expanded)
%              Number of equality atoms :   22 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f12])).

fof(f12,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(f54,plain,(
    ~ r3_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f46,f37])).

fof(f37,plain,
    ( sK0 = sK1
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f35,f10])).

fof(f10,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <~> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) )
      <=> r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

fof(f35,plain,
    ( r3_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f32,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f32,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | r3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = sK1
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f29,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f29,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f28,f13])).

fof(f28,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f11,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f45,f39])).

fof(f39,plain,
    ( sK0 = sK1
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f35,f8])).

fof(f8,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f34,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f30,f15])).

fof(f48,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f9,f47])).

fof(f9,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
