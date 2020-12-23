%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 720 expanded)
%              Number of leaves         :   11 ( 183 expanded)
%              Depth                    :   27
%              Number of atoms          :  281 (4145 expanded)
%              Number of equality atoms :   18 ( 128 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f522,plain,(
    $false ),
    inference(subsumption_resolution,[],[f515,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f515,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f498,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f498,plain,(
    r2_hidden(sK2(sK4,sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f489,f494])).

fof(f494,plain,(
    r2_hidden(sK2(sK4,sK3),sK3) ),
    inference(resolution,[],[f485,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] : sP1(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f485,plain,(
    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f483,f456])).

fof(f456,plain,(
    sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f36,f451])).

fof(f451,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,sK4) ),
    inference(superposition,[],[f42,f442])).

fof(f442,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f441,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f441,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | r1_xboole_0(sK3,sK4) ),
    inference(resolution,[],[f436,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X1,X0)
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X1,X0)
        & ? [X2] :
            ( r2_hidden(X2,X0)
            & r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f17])).

% (20152)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f17,plain,(
    ! [X1,X0] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f436,plain,
    ( sP0(sK4,sK3)
    | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(resolution,[],[f432,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

% (20159)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f432,plain,
    ( sP1(sK4,sK3,k1_xboole_0)
    | sP0(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( sP0(sK4,sK3)
    | sP1(sK4,sK3,k1_xboole_0)
    | sP1(sK4,sK3,k1_xboole_0) ),
    inference(resolution,[],[f235,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,k1_xboole_0),X1)
      | sP1(X0,X1,k1_xboole_0) ) ),
    inference(condensation,[],[f130])).

fof(f130,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(X7,X8,k1_xboole_0),X9)
      | r2_hidden(sK5(X7,X8,k1_xboole_0),X8)
      | sP1(X7,X8,k1_xboole_0) ) ),
    inference(resolution,[],[f98,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f92,f44])).

fof(f92,plain,(
    ! [X1] : sP1(X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f87,f53])).

fof(f87,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X4)
      | sP1(X3,X4,X4) ) ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X1)
      | sP1(X0,X1,X1) ) ),
    inference(factoring,[],[f46])).

fof(f235,plain,(
    ! [X13] :
      ( ~ r2_hidden(sK5(sK4,X13,k1_xboole_0),sK3)
      | sP0(sK4,sK3)
      | sP1(sK4,X13,k1_xboole_0) ) ),
    inference(resolution,[],[f150,f37])).

fof(f37,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK4)
      | sP0(sK4,sK3)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sP0(sK4,sK3)
    | ( ! [X2] :
          ( ~ r2_hidden(X2,sK4)
          | ~ r2_hidden(X2,sK3) )
      & ~ r1_xboole_0(sK3,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( sP0(X1,X0)
        | ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) )
   => ( sP0(sK4,sK3)
      | ( ! [X2] :
            ( ~ r2_hidden(X2,sK4)
            | ~ r2_hidden(X2,sK3) )
        & ~ r1_xboole_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( sP0(X1,X0)
      | ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( sP0(X1,X0)
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(definition_folding,[],[f11,f13])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

% (20161)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f7,conjecture,(
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

fof(f150,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,k1_xboole_0),X0)
      | sP1(X0,X1,k1_xboole_0) ) ),
    inference(condensation,[],[f143])).

fof(f143,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(X7,X8,k1_xboole_0),X7)
      | sP1(X7,X8,k1_xboole_0)
      | r2_hidden(sK5(X7,X8,k1_xboole_0),X9) ) ),
    inference(resolution,[],[f47,f98])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,
    ( sP0(sK4,sK3)
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f483,plain,
    ( r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK3))
    | ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f452,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f452,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK4,sK3),X0)
      | r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f74,f451])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK3,sK4)
      | ~ r2_hidden(sK2(sK4,sK3),X0)
      | r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,X0)) ) ),
    inference(resolution,[],[f72,f36])).

fof(f72,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X3,X4)
      | r2_hidden(sK2(X3,X4),k3_xboole_0(X3,X5))
      | ~ r2_hidden(sK2(X3,X4),X5) ) ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k3_xboole_0(X2,X1)) ) ),
    inference(resolution,[],[f45,f52])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f489,plain,
    ( ~ r2_hidden(sK2(sK4,sK3),sK3)
    | r2_hidden(sK2(sK4,sK3),k1_xboole_0) ),
    inference(resolution,[],[f487,f463])).

fof(f463,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f444,f45])).

fof(f444,plain,(
    sP1(sK4,sK3,k1_xboole_0) ),
    inference(superposition,[],[f52,f442])).

fof(f487,plain,(
    r2_hidden(sK2(sK4,sK3),sK4) ),
    inference(forward_demodulation,[],[f486,f291])).

fof(f291,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(resolution,[],[f287,f50])).

fof(f287,plain,(
    ! [X0] : sP1(X0,X0,X0) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X0] :
      ( sP1(X0,X0,X0)
      | sP1(X0,X0,X0) ) ),
    inference(resolution,[],[f264,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | sP1(X0,X1,X0) ) ),
    inference(factoring,[],[f47])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X0),X1)
      | sP1(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f263,f148])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X0),X0)
      | ~ r2_hidden(sK5(X0,X1,X0),X1)
      | sP1(X0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X0),X0)
      | ~ r2_hidden(sK5(X0,X1,X0),X1)
      | sP1(X0,X1,X0)
      | sP1(X0,X1,X0) ) ),
    inference(resolution,[],[f48,f148])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f486,plain,(
    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK4)) ),
    inference(subsumption_resolution,[],[f484,f456])).

fof(f484,plain,
    ( r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK4))
    | ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f452,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (20156)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (20147)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (20154)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (20175)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (20151)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20167)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (20149)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20167)Refutation not found, incomplete strategy% (20167)------------------------------
% 0.21/0.53  % (20167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20166)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (20169)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (20154)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (20150)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f522,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f515,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f38,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.21/0.53  fof(f515,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f498,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f498,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),k1_xboole_0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f489,f494])).
% 0.21/0.53  fof(f494,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),sK3)),
% 0.21/0.53    inference(resolution,[],[f485,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(resolution,[],[f44,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X1,X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.21/0.53    inference(definition_folding,[],[f3,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f485,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f483,f456])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    sP0(sK4,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f36,f451])).
% 0.21/0.53  fof(f451,plain,(
% 0.21/0.53    r1_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f443])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(superposition,[],[f42,f442])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f441,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k1_xboole_0 != k3_xboole_0(X0,X1)) & (k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k1_xboole_0 = k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(sK3,sK4) | r1_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(resolution,[],[f436,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X1,X0) & (r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1))) | ~sP0(X0,X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X1,X0) & ? [X2] : (r2_hidden(X2,X0) & r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f17])).
% 0.21/0.53  % (20152)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X1,X0] : ((r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X1,X0] : ((r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f436,plain,(
% 0.21/0.53    sP0(sK4,sK3) | k1_xboole_0 = k3_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(resolution,[],[f432,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  % (20159)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    sP1(sK4,sK3,k1_xboole_0) | sP0(sK4,sK3)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f429])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    sP0(sK4,sK3) | sP1(sK4,sK3,k1_xboole_0) | sP1(sK4,sK3,k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f235,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,k1_xboole_0),X1) | sP1(X0,X1,k1_xboole_0)) )),
% 0.21/0.53    inference(condensation,[],[f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X8,X7,X9] : (r2_hidden(sK5(X7,X8,k1_xboole_0),X9) | r2_hidden(sK5(X7,X8,k1_xboole_0),X8) | sP1(X7,X8,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f98,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f92,f44])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X1] : (sP1(X1,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f87,f53])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~v1_xboole_0(X4) | sP1(X3,X4,X4)) )),
% 0.21/0.53    inference(resolution,[],[f85,f40])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | sP1(X0,X1,X1)) )),
% 0.21/0.53    inference(factoring,[],[f46])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X13] : (~r2_hidden(sK5(sK4,X13,k1_xboole_0),sK3) | sP0(sK4,sK3) | sP1(sK4,X13,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f150,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK4) | sP0(sK4,sK3) | ~r2_hidden(X2,sK3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    sP0(sK4,sK3) | (! [X2] : (~r2_hidden(X2,sK4) | ~r2_hidden(X2,sK3)) & ~r1_xboole_0(sK3,sK4))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1] : (sP0(X1,X0) | (! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1))) => (sP0(sK4,sK3) | (! [X2] : (~r2_hidden(X2,sK4) | ~r2_hidden(X2,sK3)) & ~r1_xboole_0(sK3,sK4)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1] : (sP0(X1,X0) | (! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : (sP0(X1,X0) | (! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(definition_folding,[],[f11,f13])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) | (! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  % (20161)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,k1_xboole_0),X0) | sP1(X0,X1,k1_xboole_0)) )),
% 0.21/0.53    inference(condensation,[],[f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X8,X7,X9] : (r2_hidden(sK5(X7,X8,k1_xboole_0),X7) | sP1(X7,X8,k1_xboole_0) | r2_hidden(sK5(X7,X8,k1_xboole_0),X9)) )),
% 0.21/0.53    inference(resolution,[],[f47,f98])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    sP0(sK4,sK3) | ~r1_xboole_0(sK3,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f483,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK3)) | ~sP0(sK4,sK3)),
% 0.21/0.53    inference(resolution,[],[f452,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f452,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK2(sK4,sK3),X0) | r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f451])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(sK3,sK4) | ~r2_hidden(sK2(sK4,sK3),X0) | r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,X0))) )),
% 0.21/0.53    inference(resolution,[],[f72,f36])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~sP0(X3,X4) | r2_hidden(sK2(X3,X4),k3_xboole_0(X3,X5)) | ~r2_hidden(sK2(X3,X4),X5)) )),
% 0.21/0.53    inference(resolution,[],[f68,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k3_xboole_0(X2,X1))) )),
% 0.21/0.53    inference(resolution,[],[f45,f52])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f489,plain,(
% 0.21/0.53    ~r2_hidden(sK2(sK4,sK3),sK3) | r2_hidden(sK2(sK4,sK3),k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f487,f463])).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f444,f45])).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    sP1(sK4,sK3,k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f52,f442])).
% 0.21/0.53  fof(f487,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),sK4)),
% 0.21/0.53    inference(forward_demodulation,[],[f486,f291])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    ( ! [X6] : (k3_xboole_0(X6,X6) = X6) )),
% 0.21/0.53    inference(resolution,[],[f287,f50])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ( ! [X0] : (sP1(X0,X0,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f268])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ( ! [X0] : (sP1(X0,X0,X0) | sP1(X0,X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f264,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X0),X0) | sP1(X0,X1,X0)) )),
% 0.21/0.53    inference(factoring,[],[f47])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1,X0),X1) | sP1(X0,X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f263,f148])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1,X0),X0) | ~r2_hidden(sK5(X0,X1,X0),X1) | sP1(X0,X1,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f244])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1,X0),X0) | ~r2_hidden(sK5(X0,X1,X0),X1) | sP1(X0,X1,X0) | sP1(X0,X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f48,f148])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f486,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f484,f456])).
% 0.21/0.53  fof(f484,plain,(
% 0.21/0.53    r2_hidden(sK2(sK4,sK3),k3_xboole_0(sK4,sK4)) | ~sP0(sK4,sK3)),
% 0.21/0.53    inference(resolution,[],[f452,f34])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (20154)------------------------------
% 0.21/0.53  % (20154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20154)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (20154)Memory used [KB]: 6524
% 0.21/0.53  % (20154)Time elapsed: 0.122 s
% 0.21/0.53  % (20154)------------------------------
% 0.21/0.53  % (20154)------------------------------
% 0.21/0.54  % (20172)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (20148)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20146)Success in time 0.177 s
%------------------------------------------------------------------------------
