%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0027+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  53 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 234 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f18,plain,(
    sK0 != k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != k3_xboole_0(sK1,sK2)
    & ! [X3] :
        ( r1_tarski(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X3,sK1) )
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( sK0 != k3_xboole_0(sK1,sK2)
      & ! [X3] :
          ( r1_tarski(X3,sK0)
          | ~ r1_tarski(X3,sK2)
          | ~ r1_tarski(X3,sK1) )
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f78,plain,(
    sK0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f77,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f77,plain,(
    sK0 = k3_xboole_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f74,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f72,f27])).

% (29359)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f19,f20])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK2,X0),sK1)
      | ~ r1_tarski(sK0,X0)
      | sK0 = k3_xboole_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f68,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,sK2)
      | sK0 = k3_xboole_0(sK2,X0)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(k3_xboole_0(sK2,X0),sK1) ) ),
    inference(resolution,[],[f65,f19])).

fof(f65,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k3_xboole_0(X4,X3),sK2)
      | ~ r1_tarski(sK0,X4)
      | sK0 = k3_xboole_0(X4,X3)
      | ~ r1_tarski(sK0,X3)
      | ~ r1_tarski(k3_xboole_0(X4,X3),sK1) ) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | sK0 = X1
      | ~ r1_tarski(X1,sK2)
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

%------------------------------------------------------------------------------
