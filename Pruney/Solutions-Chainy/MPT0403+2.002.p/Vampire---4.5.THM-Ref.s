%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 281 expanded)
%              Number of equality atoms :   37 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f217,plain,(
    ~ sP0(sK1,sK1,k2_setfam_1(sK1,sK1)) ),
    inference(resolution,[],[f194,f66])).

fof(f66,plain,(
    ~ r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),k2_setfam_1(sK1,sK1)) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK1,k2_setfam_1(sK1,sK1)),X0)
      | ~ r2_hidden(X0,k2_setfam_1(sK1,sK1)) ) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK2(X0,X1),X3)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f26,plain,(
    ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK1,k2_setfam_1(sK1,sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).

fof(f194,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),X0)
      | ~ sP0(sK1,sK1,X0) ) ),
    inference(resolution,[],[f174,f58])).

fof(f58,plain,(
    ! [X14,X13] :
      ( sP8(X14,X13,sK2(sK1,k2_setfam_1(sK1,sK1)))
      | ~ sP0(sK1,X13,X14) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X2,X0,X10,X1] :
      ( ~ r2_hidden(X10,X0)
      | ~ sP0(X0,X1,X2)
      | sP8(X2,X1,X10) ) ),
    inference(cnf_transformation,[],[f47_D])).

fof(f47_D,plain,(
    ! [X10,X1,X2] :
      ( ! [X0] :
          ( ~ r2_hidden(X10,X0)
          | ~ sP0(X0,X1,X2) )
    <=> ~ sP8(X2,X1,X10) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f49,plain,(
    r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),sK1) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f174,plain,(
    ! [X0] :
      ( ~ sP8(X0,sK1,sK2(sK1,k2_setfam_1(sK1,sK1)))
      | r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),X0) ) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(sK1,k2_setfam_1(sK1,sK1)),X0)
      | ~ sP8(X1,sK1,X0)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f59,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f59,plain,(
    ! [X15,X16] :
      ( r2_hidden(k2_xboole_0(sK2(sK1,k2_setfam_1(sK1,sK1)),X15),X16)
      | ~ sP8(X16,sK1,X15) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),X2)
      | ~ r2_hidden(X9,X1)
      | ~ sP8(X2,X1,X10) ) ),
    inference(general_splitting,[],[f45,f47_D])).

fof(f45,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (2251)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (2251)Refutation not found, incomplete strategy% (2251)------------------------------
% 0.22/0.48  % (2251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2251)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (2251)Memory used [KB]: 10490
% 0.22/0.48  % (2251)Time elapsed: 0.054 s
% 0.22/0.48  % (2251)------------------------------
% 0.22/0.48  % (2251)------------------------------
% 0.22/0.49  % (2273)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.49  % (2273)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f217,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP0(X1,X0,k2_setfam_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_setfam_1(X0,X1) != X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.49    inference(definition_folding,[],[f4,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    ~sP0(sK1,sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.49    inference(resolution,[],[f194,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),k2_setfam_1(sK1,sK1))),
% 0.22/0.49    inference(resolution,[],[f50,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK2(sK1,k2_setfam_1(sK1,sK1)),X0) | ~r2_hidden(X0,k2_setfam_1(sK1,sK1))) )),
% 0.22/0.49    inference(resolution,[],[f26,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0)) => ~r1_setfam_1(sK1,k2_setfam_1(sK1,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),X0) | ~sP0(sK1,sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f174,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X14,X13] : (sP8(X14,X13,sK2(sK1,k2_setfam_1(sK1,sK1))) | ~sP0(sK1,X13,X14)) )),
% 0.22/0.49    inference(resolution,[],[f49,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X10,X1] : (~r2_hidden(X10,X0) | ~sP0(X0,X1,X2) | sP8(X2,X1,X10)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f47_D])).
% 0.22/0.49  fof(f47_D,plain,(
% 0.22/0.49    ( ! [X10,X1,X2] : (( ! [X0] : (~r2_hidden(X10,X0) | ~sP0(X0,X1,X2)) ) <=> ~sP8(X2,X1,X10)) )),
% 0.22/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),sK1)),
% 0.22/0.49    inference(resolution,[],[f26,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X0] : (~sP8(X0,sK1,sK2(sK1,k2_setfam_1(sK1,sK1))) | r2_hidden(sK2(sK1,k2_setfam_1(sK1,sK1)),X0)) )),
% 0.22/0.49    inference(resolution,[],[f96,f44])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(sK2(sK1,k2_setfam_1(sK1,sK1)),X0) | ~sP8(X1,sK1,X0) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(superposition,[],[f59,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X15,X16] : (r2_hidden(k2_xboole_0(sK2(sK1,k2_setfam_1(sK1,sK1)),X15),X16) | ~sP8(X16,sK1,X15)) )),
% 0.22/0.49    inference(resolution,[],[f49,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X10,X1,X9] : (r2_hidden(k2_xboole_0(X9,X10),X2) | ~r2_hidden(X9,X1) | ~sP8(X2,X1,X10)) )),
% 0.22/0.49    inference(general_splitting,[],[f45,f47_D])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k2_xboole_0(X9,X10),X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.49    inference(equality_resolution,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X8,X1,X0] : (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.49    inference(rectify,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (2273)------------------------------
% 0.22/0.49  % (2273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2273)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (2273)Memory used [KB]: 1791
% 0.22/0.49  % (2273)Time elapsed: 0.072 s
% 0.22/0.49  % (2273)------------------------------
% 0.22/0.49  % (2273)------------------------------
% 0.22/0.50  % (2249)Success in time 0.134 s
%------------------------------------------------------------------------------
