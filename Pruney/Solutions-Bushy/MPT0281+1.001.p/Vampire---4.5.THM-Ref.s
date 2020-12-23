%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0281+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 317 expanded)
%              Number of leaves         :   11 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :  260 (1525 expanded)
%              Number of equality atoms :   35 ( 219 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f780,plain,(
    $false ),
    inference(global_subsumption,[],[f55,f583])).

fof(f583,plain,(
    r1_tarski(sK2,sK1) ),
    inference(backward_demodulation,[],[f67,f579])).

fof(f579,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(global_subsumption,[],[f54,f466])).

fof(f466,plain,
    ( r1_tarski(sK1,sK2)
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f101,f440])).

fof(f440,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f436,f107])).

fof(f107,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK1)
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f101,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f436,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),sK1)
    | sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f432,f71])).

fof(f71,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK2)
    | sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f67,f30])).

fof(f432,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),sK2)
    | r1_tarski(k2_xboole_0(sK1,sK2),sK1) ),
    inference(resolution,[],[f428,f48])).

% (28182)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f48,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

% (28183)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

% (28194)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f428,plain,
    ( r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k2_xboole_0(sK1,sK2),sK2) ),
    inference(resolution,[],[f427,f48])).

fof(f427,plain,
    ( r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f424,f57])).

fof(f57,plain,(
    sP0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f49,f26])).

fof(f26,plain,(
    k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)) = k1_zfmisc_1(k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r3_xboole_0(sK1,sK2)
    & k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)) = k1_zfmisc_1(k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK1,sK2)
      & k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)) = k1_zfmisc_1(k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

% (28191)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f10])).

fof(f10,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f424,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(X3,X2,k1_zfmisc_1(X1))
      | r2_hidden(X1,X3)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f422,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f422,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(condensation,[],[f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f91,f49])).

fof(f91,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X8,X7,k2_xboole_0(X9,k1_zfmisc_1(X6)))
      | r2_hidden(X6,X8)
      | r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f37,f66])).

fof(f66,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(X1,k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(k1_zfmisc_1(X0),X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(general_splitting,[],[f39,f50_D])).

fof(f50,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f50_D])).

fof(f50_D,plain,(
    ! [X0,X2] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X0)
          | r2_hidden(X4,X2) )
    <=> ~ sP5(X2,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP5(X0,k1_zfmisc_1(X1))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | sP5(X1,k1_zfmisc_1(X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f100,f48])).

fof(f100,plain,(
    r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f98,f57])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,k1_zfmisc_1(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f96,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(general_splitting,[],[f38,f52_D])).

fof(f52,plain,(
    ! [X4,X2,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2)
      | sP6(X2,X1) ) ),
    inference(cnf_transformation,[],[f52_D])).

fof(f52_D,plain,(
    ! [X1,X2] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | r2_hidden(X4,X2) )
    <=> ~ sP6(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP6(X0,k1_zfmisc_1(X1))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | sP6(X1,k1_zfmisc_1(X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f52,f47])).

fof(f54,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ~ r3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f67,plain,(
    r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f65,f48])).

fof(f65,plain,(
    r2_hidden(sK2,k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f64,f57])).

fof(f55,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

% (28175)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark

%------------------------------------------------------------------------------
