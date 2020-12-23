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
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 237 expanded)
%              Number of equality atoms :   37 (  38 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f87])).

fof(f87,plain,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_setfam_1(X0,k2_setfam_1(X0,X0))
      | r1_setfam_1(X0,k2_setfam_1(X0,X0)) ) ),
    inference(resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
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
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X0))
      | r1_setfam_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X0))
      | r1_setfam_1(X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X2))
      | r1_setfam_1(X0,X1) ) ),
    inference(superposition,[],[f74,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_xboole_0(sK2(X0,X1),X2),k2_setfam_1(X0,X3))
      | ~ r2_hidden(X2,X3)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_setfam_1(X0,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X1,X2,X4)
      | r2_hidden(k2_xboole_0(sK2(X2,X3),X0),X4)
      | ~ r2_hidden(X0,X1)
      | r1_setfam_1(X2,X3) ) ),
    inference(resolution,[],[f45,f31])).

fof(f45,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ r2_hidden(X9,X1)
      | ~ r2_hidden(X10,X0)
      | r2_hidden(k2_xboole_0(X9,X10),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k2_xboole_0(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X0)
                & r2_hidden(sK6(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k2_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k2_xboole_0(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k2_xboole_0(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k2_xboole_0(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(sK4(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k2_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X0)
        & r2_hidden(sK6(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k2_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k2_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11738)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (11738)Refutation not found, incomplete strategy% (11738)------------------------------
% 0.22/0.51  % (11738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11735)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (11754)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (11738)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11738)Memory used [KB]: 6012
% 0.22/0.51  % (11738)Time elapsed: 0.084 s
% 0.22/0.51  % (11738)------------------------------
% 0.22/0.51  % (11738)------------------------------
% 0.22/0.51  % (11735)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f26,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (r1_setfam_1(X0,k2_setfam_1(X0,X0))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (r1_setfam_1(X0,k2_setfam_1(X0,X0)) | r1_setfam_1(X0,k2_setfam_1(X0,X0))) )),
% 0.22/0.51    inference(resolution,[],[f80,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f32,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r1_tarski(sK2(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X0)) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X0)) | r1_setfam_1(X0,X1) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f78,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | r2_hidden(sK2(X0,X1),k2_setfam_1(X0,X2)) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(superposition,[],[f74,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.51    inference(rectify,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_xboole_0(sK2(X0,X1),X2),k2_setfam_1(X0,X3)) | ~r2_hidden(X2,X3) | r1_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f53,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP0(X1,X0,k2_setfam_1(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_setfam_1(X0,X1) != X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.51    inference(definition_folding,[],[f4,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~sP0(X1,X2,X4) | r2_hidden(k2_xboole_0(sK2(X2,X3),X0),X4) | ~r2_hidden(X0,X1) | r1_setfam_1(X2,X3)) )),
% 0.22/0.51    inference(resolution,[],[f45,f31])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X10,X1,X9] : (~r2_hidden(X9,X1) | ~r2_hidden(X10,X0) | r2_hidden(k2_xboole_0(X9,X10),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X8,X1,X0] : (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0)) => ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (11735)------------------------------
% 0.22/0.51  % (11735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11735)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (11735)Memory used [KB]: 6140
% 0.22/0.51  % (11735)Time elapsed: 0.096 s
% 0.22/0.51  % (11735)------------------------------
% 0.22/0.51  % (11735)------------------------------
% 0.22/0.51  % (11733)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (11731)Success in time 0.148 s
%------------------------------------------------------------------------------
