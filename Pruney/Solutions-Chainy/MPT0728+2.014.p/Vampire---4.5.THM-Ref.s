%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  255 ( 274 expanded)
%              Number of equality atoms :  151 ( 170 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X4
              & sK2(X0,X1,X2,X3,X4,X5) != X3
              & sK2(X0,X1,X2,X3,X4,X5) != X2
              & sK2(X0,X1,X2,X3,X4,X5) != X1
              & sK2(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK2(X0,X1,X2,X3,X4,X5) = X4
            | sK2(X0,X1,X2,X3,X4,X5) = X3
            | sK2(X0,X1,X2,X3,X4,X5) = X2
            | sK2(X0,X1,X2,X3,X4,X5) = X1
            | sK2(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X4
            & sK2(X0,X1,X2,X3,X4,X5) != X3
            & sK2(X0,X1,X2,X3,X4,X5) != X2
            & sK2(X0,X1,X2,X3,X4,X5) != X1
            & sK2(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK2(X0,X1,X2,X3,X4,X5) = X4
          | sK2(X0,X1,X2,X3,X4,X5) = X3
          | sK2(X0,X1,X2,X3,X4,X5) = X2
          | sK2(X0,X1,X2,X3,X4,X5) = X1
          | sK2(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f76,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ~ r2_hidden(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f25,f54])).

fof(f54,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f27,f52,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f25,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0))
   => ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f18,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (23967)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (23967)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23986)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (23992)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f76,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7))) )),
% 0.22/0.54    inference(equality_resolution,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X7) != X5) )),
% 0.22/0.54    inference(equality_resolution,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK2(X0,X1,X2,X3,X4,X5) != X4 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X4 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK2(X0,X1,X2,X3,X4,X5) != X4 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X4 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(rectify,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(resolution,[],[f62,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f27,f52,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f51])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0)) => ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f52])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (23967)------------------------------
% 0.22/0.54  % (23967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23967)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (23967)Memory used [KB]: 10746
% 0.22/0.54  % (23967)Time elapsed: 0.119 s
% 0.22/0.54  % (23967)------------------------------
% 0.22/0.54  % (23967)------------------------------
% 0.22/0.55  % (23961)Success in time 0.181 s
%------------------------------------------------------------------------------
