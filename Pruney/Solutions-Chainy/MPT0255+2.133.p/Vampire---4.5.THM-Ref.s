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
% DateTime   : Thu Dec  3 12:39:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 ( 242 expanded)
%              Number of equality atoms :  134 ( 160 expanded)
%              Maximal formula depth    :   26 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(resolution,[],[f148,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] : sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | X0 != X10 ) ),
    inference(cnf_transformation,[],[f25])).

% (26399)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9
          & X0 != X10 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | X0 = X10
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f148,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : ~ sP0(sK2,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(resolution,[],[f97,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(sK2,X0) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    k1_xboole_0 = k1_tarski(sK2) ),
    inference(forward_demodulation,[],[f68,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f68,plain,(
    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK2),k1_xboole_0) ),
    inference(superposition,[],[f30,f66])).

fof(f66,plain,(
    k1_xboole_0 = k2_tarski(sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK2,sK3) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f70,plain,(
    ! [X0] :
      ( k4_xboole_0(k1_xboole_0,X0) != k1_tarski(sK2)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(superposition,[],[f32,f66])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X0,k8_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ),
    inference(resolution,[],[f37,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ),
    inference(definition_folding,[],[f11,f13,f12])).

% (26400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ( X9 = X11
            | X8 = X11
            | X7 = X11
            | X6 = X11
            | X5 = X11
            | X4 = X11
            | X3 = X11
            | X2 = X11
            | X1 = X11
            | X0 = X11 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X9 != X11
              & X8 != X11
              & X7 != X11
              & X6 != X11
              & X5 != X11
              & X4 != X11
              & X3 != X11
              & X2 != X11
              & X1 != X11
              & X0 != X11 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_enumset1)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X12,X10) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X12,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X11] :
          ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X11,X10) )
          & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X11,X10) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ? [X11] :
            ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X12,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ? [X11] :
            ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X10)
              | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(nnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26395)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.47  % (26395)Refutation not found, incomplete strategy% (26395)------------------------------
% 0.21/0.47  % (26395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26395)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (26395)Memory used [KB]: 10618
% 0.21/0.47  % (26395)Time elapsed: 0.064 s
% 0.21/0.47  % (26395)------------------------------
% 0.21/0.47  % (26395)------------------------------
% 0.21/0.48  % (26406)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (26406)Refutation not found, incomplete strategy% (26406)------------------------------
% 0.21/0.48  % (26406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26406)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (26406)Memory used [KB]: 10618
% 0.21/0.48  % (26406)Time elapsed: 0.061 s
% 0.21/0.48  % (26406)------------------------------
% 0.21/0.48  % (26406)------------------------------
% 0.21/0.48  % (26421)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.48  % (26412)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (26412)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f148,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] : (sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | X0 != X10) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % (26399)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9 & X0 != X10)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | X0 = X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & ((X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11) | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~sP0(sK2,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 0.21/0.49    inference(resolution,[],[f97,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | ~r2_hidden(sK2,X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    k1_xboole_0 = k1_tarski(sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f68,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK2),k1_xboole_0)),
% 0.21/0.49    inference(superposition,[],[f30,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    k1_xboole_0 = k2_tarski(sK2,sK3)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK2,sK3)),
% 0.21/0.49    inference(superposition,[],[f31,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) != k1_tarski(sK2) | ~r2_hidden(sK2,X0)) )),
% 0.21/0.49    inference(superposition,[],[f32,f66])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) | ~r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (r2_hidden(X0,k8_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) )),
% 0.21/0.49    inference(resolution,[],[f37,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))) )),
% 0.21/0.49    inference(equality_resolution,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10))),
% 0.21/0.49    inference(definition_folding,[],[f11,f13,f12])).
% 0.21/0.49  % (26400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) <=> ! [X11] : (r2_hidden(X11,X10) <=> sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> ~(X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_enumset1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X12,X10)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)))) & (! [X12] : ((r2_hidden(X12,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X12,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10)))) & (! [X12] : ((r2_hidden(X12,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X12,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 0.21/0.49    inference(rectify,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10)))) & (! [X11] : ((r2_hidden(X11,X10) | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26412)------------------------------
% 0.21/0.49  % (26412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26412)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26412)Memory used [KB]: 1663
% 0.21/0.49  % (26412)Time elapsed: 0.095 s
% 0.21/0.49  % (26412)------------------------------
% 0.21/0.49  % (26412)------------------------------
% 0.21/0.49  % (26391)Success in time 0.131 s
%------------------------------------------------------------------------------
