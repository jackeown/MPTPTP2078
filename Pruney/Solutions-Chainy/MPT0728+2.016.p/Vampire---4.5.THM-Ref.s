%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:10 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  72 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  279 ( 304 expanded)
%              Number of equality atoms :  176 ( 201 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f71,f60,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f19,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

% (12578)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f60,plain,(
    ~ r2_hidden(sK0,k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f26,f59])).

fof(f59,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f28,f57,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f56])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f26,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).

fof(f14,plain,
    ( ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0))
   => ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f71,plain,(
    ! [X4,X2,X0,X8,X3,X1] : r2_hidden(X8,k4_enumset1(X0,X1,X2,X3,X4,X8)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X8) != X6 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6) != X5
              & sK2(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK2(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK2(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK2(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK2(X0,X1,X2,X3,X4,X5,X6) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK2(X0,X1,X2,X3,X4,X5,X6) = X5
            | sK2(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK2(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK2(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK2(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK2(X0,X1,X2,X3,X4,X5,X6) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6) != X5
            & sK2(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK2(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK2(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK2(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK2(X0,X1,X2,X3,X4,X5,X6) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK2(X0,X1,X2,X3,X4,X5,X6) = X5
          | sK2(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK2(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK2(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK2(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK2(X0,X1,X2,X3,X4,X5,X6) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(rectify,[],[f22])).

% (12565)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.50/0.56  % (12559)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.57  % (12556)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.58  % (12575)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.58  % (12583)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.58  % (12581)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.59  % (12555)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.59  % (12557)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.59  % (12558)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.59  % (12581)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % (12561)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f85,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(unit_resulting_resolution,[],[f71,f60,f67])).
% 1.50/0.59  fof(f67,plain,(
% 1.50/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f64])).
% 1.50/0.59  fof(f64,plain,(
% 1.50/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.50/0.59    inference(definition_unfolding,[],[f34,f57])).
% 1.50/0.59  fof(f57,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.59    inference(definition_unfolding,[],[f29,f56])).
% 1.50/0.59  fof(f56,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.59    inference(definition_unfolding,[],[f30,f55])).
% 1.50/0.59  fof(f55,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.59    inference(definition_unfolding,[],[f31,f54])).
% 1.50/0.59  fof(f54,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.59    inference(definition_unfolding,[],[f38,f39])).
% 1.50/0.59  fof(f39,plain,(
% 1.50/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f6])).
% 1.50/0.59  fof(f6,axiom,(
% 1.50/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.59  fof(f38,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f5])).
% 1.50/0.59  fof(f5,axiom,(
% 1.50/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.59  fof(f31,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f4])).
% 1.50/0.59  fof(f4,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.59  fof(f30,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f3])).
% 1.50/0.59  fof(f3,axiom,(
% 1.50/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.59  fof(f29,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f7])).
% 1.50/0.59  fof(f7,axiom,(
% 1.50/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.59  fof(f34,plain,(
% 1.50/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.59    inference(cnf_transformation,[],[f20])).
% 1.50/0.59  fof(f20,plain,(
% 1.50/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 1.50/0.59  fof(f19,plain,(
% 1.50/0.59    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f18,plain,(
% 1.50/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.59    inference(rectify,[],[f17])).
% 1.50/0.59  fof(f17,plain,(
% 1.50/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.59    inference(flattening,[],[f16])).
% 1.50/0.60  % (12578)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.60  fof(f16,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.60    inference(nnf_transformation,[],[f1])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.50/0.60  fof(f60,plain,(
% 1.50/0.60    ~r2_hidden(sK0,k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.50/0.60    inference(definition_unfolding,[],[f26,f59])).
% 1.50/0.60  fof(f59,plain,(
% 1.50/0.60    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X0,X0,X0,X0,X0,X0)))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f28,f57,f58])).
% 1.50/0.60  fof(f58,plain,(
% 1.50/0.60    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f27,f56])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f2])).
% 1.50/0.60  fof(f2,axiom,(
% 1.50/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.60  fof(f28,plain,(
% 1.50/0.60    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f9])).
% 1.50/0.60  fof(f9,axiom,(
% 1.50/0.60    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.50/0.60    inference(cnf_transformation,[],[f15])).
% 1.50/0.60  fof(f15,plain,(
% 1.50/0.60    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).
% 1.50/0.60  fof(f14,plain,(
% 1.50/0.60    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0)) => ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f12,plain,(
% 1.50/0.60    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f11])).
% 1.50/0.60  fof(f11,negated_conjecture,(
% 1.50/0.60    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.50/0.60    inference(negated_conjecture,[],[f10])).
% 1.50/0.60  fof(f10,conjecture,(
% 1.50/0.60    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.50/0.60  fof(f71,plain,(
% 1.50/0.60    ( ! [X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,k4_enumset1(X0,X1,X2,X3,X4,X8))) )),
% 1.50/0.60    inference(equality_resolution,[],[f70])).
% 1.50/0.60  fof(f70,plain,(
% 1.50/0.60    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | k4_enumset1(X0,X1,X2,X3,X4,X8) != X6) )),
% 1.50/0.60    inference(equality_resolution,[],[f46])).
% 1.50/0.60  fof(f46,plain,(
% 1.50/0.60    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.50/0.60    inference(cnf_transformation,[],[f25])).
% 1.50/0.60  fof(f25,plain,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | (((sK2(X0,X1,X2,X3,X4,X5,X6) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK2(X0,X1,X2,X3,X4,X5,X6) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 1.50/0.60  fof(f24,plain,(
% 1.50/0.60    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6))) => (((sK2(X0,X1,X2,X3,X4,X5,X6) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK2(X0,X1,X2,X3,X4,X5,X6) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f23,plain,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.50/0.60    inference(rectify,[],[f22])).
% 1.50/0.60  % (12565)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.50/0.60    inference(flattening,[],[f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.50/0.60    inference(nnf_transformation,[],[f13])).
% 1.50/0.60  fof(f13,plain,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.50/0.60    inference(ennf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 1.50/0.60  % SZS output end Proof for theBenchmark
% 1.50/0.60  % (12581)------------------------------
% 1.50/0.60  % (12581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (12581)Termination reason: Refutation
% 1.50/0.60  
% 1.50/0.60  % (12581)Memory used [KB]: 10746
% 1.50/0.60  % (12581)Time elapsed: 0.158 s
% 1.50/0.60  % (12581)------------------------------
% 1.50/0.60  % (12581)------------------------------
% 1.50/0.60  % (12560)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.60  % (12570)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.60  % (12554)Success in time 0.237 s
%------------------------------------------------------------------------------
