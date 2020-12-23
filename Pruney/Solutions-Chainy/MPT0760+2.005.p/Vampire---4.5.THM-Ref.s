%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  92 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 ( 390 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f27])).

fof(f27,plain,(
    k1_xboole_0 != k1_wellord1(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k1_wellord1(sK3,sK2)
    & ~ r2_hidden(sK2,k3_relat_1(sK3))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK3,sK2)
      & ~ r2_hidden(sK2,k3_relat_1(sK3))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(f77,plain,(
    k1_xboole_0 = k1_wellord1(sK3,sK2) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1)
      | k1_wellord1(sK3,X0) = X1 ) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_wellord1(X0,X1) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f15,f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,X1),X0)
            & X1 != X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1,X2)
      | k1_wellord1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f69,plain,(
    sP0(sK3,sK2,k1_xboole_0) ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK2,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK3))
      | sP0(sK3,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f67,f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X0,k3_relat_1(sK3))
      | sP0(sK3,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f66,f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP1(X1)
      | sP0(sK3,X0,k1_xboole_0)
      | r2_hidden(X0,k3_relat_1(sK3)) ) ),
    inference(resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k1_wellord1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X8,X7,X9] :
      ( ~ sP0(X8,sK4(sK3,X7,k1_xboole_0),X9)
      | r2_hidden(X7,k3_relat_1(sK3))
      | sP0(sK3,X7,k1_xboole_0) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X4,X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
            | sK4(X0,X1,X2) = X1
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
              & sK4(X0,X1,X2) != X1 )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
          | sK4(X0,X1,X2) = X1
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
            & sK4(X0,X1,X2) != X1 )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK3,X0,k1_xboole_0),X1)
      | sP0(sK3,X0,k1_xboole_0)
      | r2_hidden(X0,k3_relat_1(sK3)) ) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X5,X6)
      | sP0(sK3,X4,X5)
      | r2_hidden(sK4(sK3,X4,X5),X6)
      | r2_hidden(X4,k3_relat_1(sK3)) ) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK3,X0,X1),X1)
      | r2_hidden(X0,k3_relat_1(sK3))
      | sP0(sK3,X0,X1) ) ),
    inference(resolution,[],[f48,f25])).

fof(f48,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | sP0(X4,X5,X6)
      | r2_hidden(X5,k3_relat_1(X4))
      | r2_hidden(sK4(X4,X5,X6),X6) ) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (22693)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.47  % (22711)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (22693)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    k1_xboole_0 != k1_wellord1(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != k1_wellord1(sK3,sK2) & ~r2_hidden(sK2,k3_relat_1(sK3)) & v1_relat_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK3,sK2) & ~r2_hidden(sK2,k3_relat_1(sK3)) & v1_relat_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    k1_xboole_0 = k1_wellord1(sK3,sK2)),
% 0.21/0.48    inference(resolution,[],[f69,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(sK3,X0,X1) | k1_wellord1(sK3,X0) = X1) )),
% 0.21/0.48    inference(resolution,[],[f44,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f30,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(definition_folding,[],[f10,f15,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X0) | ~sP0(X0,X1,X2) | k1_wellord1(X0,X1) = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2)) | ~sP1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    sP0(sK3,sK2,k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f68,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r2_hidden(sK2,k3_relat_1(sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k3_relat_1(sK3)) | sP0(sK3,X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f67,f25])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(X0,k3_relat_1(sK3)) | sP0(sK3,X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f66,f37])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP1(X1) | sP0(sK3,X0,k1_xboole_0) | r2_hidden(X0,k3_relat_1(sK3))) )),
% 0.21/0.48    inference(resolution,[],[f63,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1,k1_wellord1(X0,X1)) | ~sP1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X8,X7,X9] : (~sP0(X8,sK4(sK3,X7,k1_xboole_0),X9) | r2_hidden(X7,k3_relat_1(sK3)) | sP0(sK3,X7,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f60,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | ~sP0(X0,X4,X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(sK3,X0,k1_xboole_0),X1) | sP0(sK3,X0,k1_xboole_0) | r2_hidden(X0,k3_relat_1(sK3))) )),
% 0.21/0.48    inference(resolution,[],[f58,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (~r1_tarski(X5,X6) | sP0(sK3,X4,X5) | r2_hidden(sK4(sK3,X4,X5),X6) | r2_hidden(X4,k3_relat_1(sK3))) )),
% 0.21/0.48    inference(resolution,[],[f56,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(sK3,X0,X1),X1) | r2_hidden(X0,k3_relat_1(sK3)) | sP0(sK3,X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f48,f25])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | sP0(X4,X5,X6) | r2_hidden(X5,k3_relat_1(X4)) | r2_hidden(sK4(X4,X5,X6),X6)) )),
% 0.21/0.48    inference(resolution,[],[f35,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22693)------------------------------
% 0.21/0.48  % (22693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22693)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22693)Memory used [KB]: 6268
% 0.21/0.48  % (22693)Time elapsed: 0.071 s
% 0.21/0.48  % (22693)------------------------------
% 0.21/0.48  % (22693)------------------------------
% 0.21/0.48  % (22685)Success in time 0.126 s
%------------------------------------------------------------------------------
