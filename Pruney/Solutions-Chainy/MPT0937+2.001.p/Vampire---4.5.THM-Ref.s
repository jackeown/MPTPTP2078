%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:58 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   16
%              Number of atoms          :  238 ( 420 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f80])).

fof(f80,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f78,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f78,plain,(
    ! [X0] :
      ( r1_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r1_relat_2(k1_wellord2(X0),X0)
      | r1_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | r1_relat_2(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f73,f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | r1_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f69,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f12,f14,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f51,plain,(
    ! [X0] :
      ( ~ sP1(X0,k1_wellord2(X0))
      | sP0(k1_wellord2(X0),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X4,X5),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_relat_2(k1_wellord2(X0),X0)
      | v1_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r1_relat_2(k1_wellord2(X0),X0)
      | v1_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f34,f60])).

fof(f60,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_relat_2(X0,k3_relat_1(X0))
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(f31,plain,(
    ~ v1_relat_2(k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ v1_relat_2(k1_wellord2(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f16])).

fof(f16,plain,
    ( ? [X0] : ~ v1_relat_2(k1_wellord2(X0))
   => ~ v1_relat_2(k1_wellord2(sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v1_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:41:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.43  % (29101)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.44  % (29101)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f81,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(subsumption_resolution,[],[f31,f80])).
% 0.18/0.44  fof(f80,plain,(
% 0.18/0.44    ( ! [X0] : (v1_relat_2(k1_wellord2(X0))) )),
% 0.18/0.44    inference(subsumption_resolution,[],[f62,f79])).
% 0.18/0.44  fof(f79,plain,(
% 0.18/0.44    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0)) )),
% 0.18/0.44    inference(subsumption_resolution,[],[f78,f32])).
% 0.18/0.44  fof(f32,plain,(
% 0.18/0.44    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f5])).
% 0.18/0.44  fof(f5,axiom,(
% 0.18/0.44    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.18/0.44  fof(f78,plain,(
% 0.18/0.44    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(duplicate_literal_removal,[],[f77])).
% 0.18/0.44  fof(f77,plain,(
% 0.18/0.44    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0) | r1_relat_2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(resolution,[],[f76,f36])).
% 0.18/0.44  fof(f36,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f22])).
% 0.18/0.44  fof(f22,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.18/0.44  fof(f21,plain,(
% 0.18/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f20,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(rectify,[],[f19])).
% 0.18/0.44  fof(f19,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(nnf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f2])).
% 0.18/0.44  fof(f2,axiom,(
% 0.18/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).
% 0.18/0.44  fof(f76,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(sK3(k1_wellord2(X0),X1),X0) | r1_relat_2(k1_wellord2(X0),X1)) )),
% 0.18/0.44    inference(subsumption_resolution,[],[f73,f32])).
% 0.18/0.44  fof(f73,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(sK3(k1_wellord2(X0),X1),X0) | r1_relat_2(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(resolution,[],[f71,f37])).
% 0.18/0.44  fof(f37,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f22])).
% 0.18/0.44  fof(f71,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) | ~r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(duplicate_literal_removal,[],[f70])).
% 0.18/0.44  fof(f70,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))) )),
% 0.18/0.44    inference(resolution,[],[f69,f56])).
% 0.18/0.44  fof(f56,plain,(
% 0.18/0.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.44    inference(equality_resolution,[],[f49])).
% 0.18/0.44  fof(f49,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.18/0.44    inference(cnf_transformation,[],[f30])).
% 0.18/0.44  fof(f30,plain,(
% 0.18/0.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.44    inference(flattening,[],[f29])).
% 0.18/0.44  fof(f29,plain,(
% 0.18/0.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.44    inference(nnf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.44  fof(f69,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) )),
% 0.18/0.44    inference(resolution,[],[f42,f59])).
% 0.18/0.44  fof(f59,plain,(
% 0.18/0.44    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.18/0.44    inference(subsumption_resolution,[],[f58,f32])).
% 0.18/0.44  fof(f58,plain,(
% 0.18/0.44    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(resolution,[],[f51,f47])).
% 0.18/0.44  fof(f47,plain,(
% 0.18/0.44    ( ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f15])).
% 0.18/0.44  fof(f15,plain,(
% 0.18/0.44    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 0.18/0.44    inference(definition_folding,[],[f12,f14,f13])).
% 0.18/0.44  fof(f13,plain,(
% 0.18/0.44    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.18/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.44  fof(f14,plain,(
% 0.18/0.44    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.18/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.44  fof(f12,plain,(
% 0.18/0.44    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.18/0.44    inference(flattening,[],[f11])).
% 0.18/0.44  fof(f11,plain,(
% 0.18/0.44    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.18/0.44    inference(ennf_transformation,[],[f4])).
% 0.18/0.44  fof(f4,axiom,(
% 0.18/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.18/0.44  fof(f51,plain,(
% 0.18/0.44    ( ! [X0] : (~sP1(X0,k1_wellord2(X0)) | sP0(k1_wellord2(X0),X0)) )),
% 0.18/0.44    inference(equality_resolution,[],[f38])).
% 0.18/0.44  fof(f38,plain,(
% 0.18/0.44    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f23])).
% 0.18/0.44  fof(f23,plain,(
% 0.18/0.44    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 0.18/0.44    inference(nnf_transformation,[],[f14])).
% 0.18/0.44  fof(f42,plain,(
% 0.18/0.44    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | r2_hidden(k4_tarski(X4,X5),X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f28])).
% 0.18/0.44  fof(f28,plain,(
% 0.18/0.44    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).
% 0.18/0.44  fof(f27,plain,(
% 0.18/0.44    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f26,plain,(
% 0.18/0.44    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.18/0.44    inference(rectify,[],[f25])).
% 0.18/0.44  fof(f25,plain,(
% 0.18/0.44    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.18/0.44    inference(flattening,[],[f24])).
% 0.18/0.44  fof(f24,plain,(
% 0.18/0.44    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.18/0.44    inference(nnf_transformation,[],[f13])).
% 0.18/0.44  fof(f62,plain,(
% 0.18/0.44    ( ! [X0] : (~r1_relat_2(k1_wellord2(X0),X0) | v1_relat_2(k1_wellord2(X0))) )),
% 0.18/0.44    inference(subsumption_resolution,[],[f61,f32])).
% 0.18/0.44  fof(f61,plain,(
% 0.18/0.44    ( ! [X0] : (~r1_relat_2(k1_wellord2(X0),X0) | v1_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.18/0.44    inference(superposition,[],[f34,f60])).
% 0.18/0.44  fof(f60,plain,(
% 0.18/0.44    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.18/0.44    inference(resolution,[],[f59,f40])).
% 0.18/0.44  fof(f40,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.18/0.44    inference(cnf_transformation,[],[f28])).
% 0.18/0.44  fof(f34,plain,(
% 0.18/0.44    ( ! [X0] : (~r1_relat_2(X0,k3_relat_1(X0)) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f18,plain,(
% 0.18/0.44    ! [X0] : (((v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0))) & (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(nnf_transformation,[],[f9])).
% 0.18/0.44  fof(f9,plain,(
% 0.18/0.44    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f3])).
% 0.18/0.44  fof(f3,axiom,(
% 0.18/0.44    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).
% 0.18/0.44  fof(f31,plain,(
% 0.18/0.44    ~v1_relat_2(k1_wellord2(sK2))),
% 0.18/0.44    inference(cnf_transformation,[],[f17])).
% 0.18/0.44  fof(f17,plain,(
% 0.18/0.44    ~v1_relat_2(k1_wellord2(sK2))),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f16])).
% 0.18/0.44  fof(f16,plain,(
% 0.18/0.44    ? [X0] : ~v1_relat_2(k1_wellord2(X0)) => ~v1_relat_2(k1_wellord2(sK2))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f8,plain,(
% 0.18/0.44    ? [X0] : ~v1_relat_2(k1_wellord2(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f7])).
% 0.18/0.44  fof(f7,negated_conjecture,(
% 0.18/0.44    ~! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.18/0.44    inference(negated_conjecture,[],[f6])).
% 0.18/0.44  fof(f6,conjecture,(
% 0.18/0.44    ! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (29101)------------------------------
% 0.18/0.44  % (29101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (29101)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (29101)Memory used [KB]: 6140
% 0.18/0.44  % (29101)Time elapsed: 0.074 s
% 0.18/0.44  % (29101)------------------------------
% 0.18/0.44  % (29101)------------------------------
% 0.18/0.44  % (29094)Success in time 0.105 s
%------------------------------------------------------------------------------
