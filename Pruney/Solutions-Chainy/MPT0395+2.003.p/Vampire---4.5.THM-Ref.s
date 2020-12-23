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
% DateTime   : Thu Dec  3 12:46:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 218 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(global_subsumption,[],[f26,f79])).

fof(f79,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    sP0(sK2,sK1,sK2) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_setfam_1(sK1,sK2)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f13])).

% (21314)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK1,sK2)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(general_splitting,[],[f34,f46_D])).

fof(f46,plain,(
    ! [X4,X2,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2)
      | sP6(X2,X1) ) ),
    inference(cnf_transformation,[],[f46_D])).

% (21312)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f46_D,plain,(
    ! [X1,X2] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | r2_hidden(X4,X2) )
    <=> ~ sP6(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP6(X0,X1)
      | r1_setfam_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP6(X0,X1)
      | r1_setfam_1(X1,X0)
      | r1_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | sP6(X2,X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ~ r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21309)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (21316)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (21308)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21315)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (21316)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(global_subsumption,[],[f26,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    r1_setfam_1(sK1,sK2)),
% 0.22/0.51    inference(resolution,[],[f76,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    sP0(sK2,sK1,sK2)),
% 0.22/0.51    inference(superposition,[],[f43,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    sK2 = k2_xboole_0(sK1,sK2)),
% 0.22/0.51    inference(resolution,[],[f27,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ~r1_setfam_1(sK1,sK2) & r1_tarski(sK1,sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f13])).
% 1.16/0.52  % (21314)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.16/0.52  fof(f13,plain,(
% 1.16/0.52    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK1,sK2) & r1_tarski(sK1,sK2))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f8,plain,(
% 1.16/0.52    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 1.16/0.52    inference(ennf_transformation,[],[f6])).
% 1.16/0.52  fof(f6,negated_conjecture,(
% 1.16/0.52    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 1.16/0.52    inference(negated_conjecture,[],[f5])).
% 1.16/0.52  fof(f5,conjecture,(
% 1.16/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 1.16/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 1.16/0.52  fof(f27,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.16/0.52    inference(cnf_transformation,[],[f9])).
% 1.16/0.52  fof(f9,plain,(
% 1.16/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.16/0.52    inference(ennf_transformation,[],[f3])).
% 1.16/0.52  fof(f3,axiom,(
% 1.16/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.16/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.16/0.52  fof(f43,plain,(
% 1.16/0.52    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 1.16/0.52    inference(equality_resolution,[],[f39])).
% 1.16/0.52  fof(f39,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.16/0.52    inference(cnf_transformation,[],[f24])).
% 1.16/0.52  fof(f24,plain,(
% 1.16/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.16/0.52    inference(nnf_transformation,[],[f12])).
% 1.16/0.52  fof(f12,plain,(
% 1.16/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.16/0.52    inference(definition_folding,[],[f1,f11])).
% 1.16/0.52  fof(f11,plain,(
% 1.16/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.16/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.16/0.52  fof(f1,axiom,(
% 1.16/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.16/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.16/0.52  fof(f76,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~sP0(X2,X0,X1) | r1_setfam_1(X0,X1)) )),
% 1.16/0.52    inference(resolution,[],[f75,f47])).
% 1.16/0.52  fof(f47,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~sP6(X2,X1) | ~sP0(X0,X1,X2)) )),
% 1.16/0.52    inference(general_splitting,[],[f34,f46_D])).
% 1.16/0.52  fof(f46,plain,(
% 1.16/0.52    ( ! [X4,X2,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X2) | sP6(X2,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f46_D])).
% 1.16/0.52  % (21312)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.16/0.52  fof(f46_D,plain,(
% 1.16/0.52    ( ! [X1,X2] : (( ! [X4] : (~r2_hidden(X4,X1) | r2_hidden(X4,X2)) ) <=> ~sP6(X2,X1)) )),
% 1.16/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.16/0.52  fof(f34,plain,(
% 1.16/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f23])).
% 1.16/0.52  fof(f23,plain,(
% 1.16/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.16/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.16/0.52  fof(f22,plain,(
% 1.16/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f21,plain,(
% 1.16/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.16/0.52    inference(rectify,[],[f20])).
% 1.16/0.52  fof(f20,plain,(
% 1.16/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.16/0.52    inference(flattening,[],[f19])).
% 1.16/0.52  fof(f19,plain,(
% 1.16/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.16/0.52    inference(nnf_transformation,[],[f11])).
% 1.16/0.52  fof(f75,plain,(
% 1.16/0.52    ( ! [X0,X1] : (sP6(X0,X1) | r1_setfam_1(X1,X0)) )),
% 1.16/0.52    inference(duplicate_literal_removal,[],[f72])).
% 1.16/0.52  fof(f72,plain,(
% 1.16/0.52    ( ! [X0,X1] : (sP6(X0,X1) | r1_setfam_1(X1,X0) | r1_setfam_1(X1,X0)) )),
% 1.16/0.52    inference(resolution,[],[f58,f59])).
% 1.16/0.52  fof(f59,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_setfam_1(X0,X1)) )),
% 1.16/0.52    inference(resolution,[],[f32,f41])).
% 1.16/0.52  fof(f41,plain,(
% 1.16/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.16/0.52    inference(equality_resolution,[],[f29])).
% 1.16/0.52  fof(f29,plain,(
% 1.16/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.16/0.52    inference(cnf_transformation,[],[f16])).
% 1.16/0.52  fof(f16,plain,(
% 1.16/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.52    inference(flattening,[],[f15])).
% 1.16/0.52  fof(f15,plain,(
% 1.16/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.52    inference(nnf_transformation,[],[f2])).
% 1.16/0.52  fof(f2,axiom,(
% 1.16/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.16/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.16/0.52  fof(f32,plain,(
% 1.16/0.52    ( ! [X0,X3,X1] : (~r1_tarski(sK3(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f18])).
% 1.16/0.52  fof(f18,plain,(
% 1.16/0.52    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.16/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).
% 1.16/0.52  fof(f17,plain,(
% 1.16/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f10,plain,(
% 1.16/0.52    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.16/0.52    inference(ennf_transformation,[],[f7])).
% 1.16/0.52  fof(f7,plain,(
% 1.16/0.52    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 1.16/0.52    inference(unused_predicate_definition_removal,[],[f4])).
% 1.16/0.52  fof(f4,axiom,(
% 1.16/0.52    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.16/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 1.16/0.52  fof(f58,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | sP6(X2,X0) | r1_setfam_1(X0,X1)) )),
% 1.16/0.52    inference(resolution,[],[f46,f31])).
% 1.16/0.52  fof(f31,plain,(
% 1.16/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f18])).
% 1.16/0.52  fof(f26,plain,(
% 1.16/0.52    ~r1_setfam_1(sK1,sK2)),
% 1.16/0.52    inference(cnf_transformation,[],[f14])).
% 1.16/0.52  % SZS output end Proof for theBenchmark
% 1.16/0.52  % (21316)------------------------------
% 1.16/0.52  % (21316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (21316)Termination reason: Refutation
% 1.16/0.52  
% 1.16/0.52  % (21316)Memory used [KB]: 6140
% 1.16/0.52  % (21316)Time elapsed: 0.097 s
% 1.16/0.52  % (21316)------------------------------
% 1.16/0.52  % (21316)------------------------------
% 1.16/0.52  % (21303)Success in time 0.147 s
%------------------------------------------------------------------------------
