%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 122 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 ( 511 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(global_subsumption,[],[f28,f96])).

fof(f96,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(resolution,[],[f95,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k6_relat_1(X0),X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP9(X0,k6_relat_1(X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X1] : sP0(X1,k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X2,X1] : sP1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f9,f11,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> ( X2 = X3
            & r2_hidden(X2,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f42,plain,(
    ! [X1] :
      ( sP0(X1,k6_relat_1(X1))
      | ~ sP1(k6_relat_1(X1),X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k6_relat_1(X1) != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k6_relat_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(X4,X0)
      | sP9(X4,X1) ) ),
    inference(cnf_transformation,[],[f46_D])).

fof(f46_D,plain,(
    ! [X1,X4] :
      ( ! [X0] :
          ( ~ sP0(X0,X1)
          | r2_hidden(X4,X0) )
    <=> ~ sP9(X4,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f85,plain,(
    ! [X6,X7] :
      ( ~ sP9(sK4(k6_relat_1(X6),X7),k6_relat_1(X6))
      | r1_tarski(k6_relat_1(X6),X7) ) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP9(X4,X1) ) ),
    inference(general_splitting,[],[f35,f46_D])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK6(X0,X1) != sK7(X0,X1)
            | ~ r2_hidden(sK6(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
          & ( ( sK6(X0,X1) = sK7(X0,X1)
              & r2_hidden(sK6(X0,X1),X0) )
            | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | X4 != X5
              | ~ r2_hidden(X4,X0) )
            & ( ( X4 = X5
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK6(X0,X1) != sK7(X0,X1)
          | ~ r2_hidden(sK6(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( ( sK6(X0,X1) = sK7(X0,X1)
            & r2_hidden(sK6(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( X2 != X3
              | ~ r2_hidden(X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( ( X2 = X3
                & r2_hidden(X2,X0) )
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | X4 != X5
              | ~ r2_hidden(X4,X0) )
            & ( ( X4 = X5
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( X2 != X3
              | ~ r2_hidden(X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( ( X2 = X3
                & r2_hidden(X2,X0) )
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | X2 != X3
              | ~ r2_hidden(X2,X0) )
            & ( ( X2 = X3
                & r2_hidden(X2,X0) )
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( X2 != X3
              | ~ r2_hidden(X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( ( X2 = X3
                & r2_hidden(X2,X0) )
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | X2 != X3
              | ~ r2_hidden(X2,X0) )
            & ( ( X2 = X3
                & r2_hidden(X2,X0) )
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK4(k6_relat_1(X1),X2),sK5(k6_relat_1(X1),X2)),k6_relat_1(X1))
      | r1_tarski(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f95,plain,(
    ~ r2_hidden(sK4(k6_relat_1(sK2),sK3),sK2) ),
    inference(resolution,[],[f94,f27])).

fof(f27,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,X2),sK3)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k6_relat_1(sK2),sK3)
    & ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK3)
        | ~ r2_hidden(X2,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        & ! [X2] :
            ( r2_hidden(k4_tarski(X2,X2),X1)
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_relat_1(sK2),sK3)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),sK3)
          | ~ r2_hidden(X2,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ( r2_hidden(X2,X0)
             => r2_hidden(k4_tarski(X2,X2),X1) )
         => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(f94,plain,(
    ~ r2_hidden(k4_tarski(sK4(k6_relat_1(sK2),sK3),sK4(k6_relat_1(sK2),sK3)),sK3) ),
    inference(global_subsumption,[],[f28,f92])).

fof(f92,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k6_relat_1(sK2),sK3),sK4(k6_relat_1(sK2),sK3)),sK3)
    | r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(superposition,[],[f67,f89])).

fof(f89,plain,(
    sK4(k6_relat_1(sK2),sK3) = sK5(k6_relat_1(sK2),sK3) ),
    inference(resolution,[],[f84,f28])).

fof(f84,plain,(
    ! [X4,X5] :
      ( r1_tarski(k6_relat_1(X4),X5)
      | sK4(k6_relat_1(X4),X5) = sK5(k6_relat_1(X4),X5) ) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
      | X0 = X1 ) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0] : sP8(k6_relat_1(X0)) ),
    inference(resolution,[],[f44,f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | sP8(X1) ) ),
    inference(cnf_transformation,[],[f44_D])).

fof(f44_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ sP0(X0,X1)
    <=> ~ sP8(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f45,plain,(
    ! [X4,X5,X1] :
      ( ~ sP8(X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | X4 = X5 ) ),
    inference(general_splitting,[],[f36,f44_D])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(k6_relat_1(X1),X2),sK5(k6_relat_1(X1),X2)),X2)
      | r1_tarski(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ~ r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:42:39 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.46  % (25530)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (25530)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(global_subsumption,[],[f28,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.47    inference(resolution,[],[f95,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK4(k6_relat_1(X0),X1),X0) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(resolution,[],[f85,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sP9(X0,k6_relat_1(X1)) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f46,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X1] : (sP0(X1,k6_relat_1(X1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f42,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X1] : (sP1(k6_relat_1(X1),X2)) )),
% 0.21/0.47    inference(resolution,[],[f41,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | sP1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (sP1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(definition_folding,[],[f9,f11,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0))))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X1,X0] : ((k6_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X1] : (sP0(X1,k6_relat_1(X1)) | ~sP1(k6_relat_1(X1),X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sP0(X1,X0) | k6_relat_1(X1) != X0 | ~sP1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (((k6_relat_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k6_relat_1(X1) != X0)) | ~sP1(X0,X1))),
% 0.21/0.47    inference(rectify,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X1,X0] : (((k6_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k6_relat_1(X0) != X1)) | ~sP1(X1,X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (~sP0(X0,X1) | r2_hidden(X4,X0) | sP9(X4,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f46_D])).
% 0.21/0.47  fof(f46_D,plain,(
% 0.21/0.47    ( ! [X1,X4] : (( ! [X0] : (~sP0(X0,X1) | r2_hidden(X4,X0)) ) <=> ~sP9(X4,X1)) )),
% 0.21/0.47    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X6,X7] : (~sP9(sK4(k6_relat_1(X6),X7),k6_relat_1(X6)) | r1_tarski(k6_relat_1(X6),X7)) )),
% 0.21/0.47    inference(resolution,[],[f64,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X4,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X1) | ~sP9(X4,X1)) )),
% 0.21/0.47    inference(general_splitting,[],[f35,f46_D])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ((sK6(X0,X1) != sK7(X0,X1) | ~r2_hidden(sK6(X0,X1),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & ((sK6(X0,X1) = sK7(X0,X1) & r2_hidden(sK6(X0,X1),X0)) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK6(X0,X1) != sK7(X0,X1) | ~r2_hidden(sK6(X0,X1),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & ((sK6(X0,X1) = sK7(X0,X1) & r2_hidden(sK6(X0,X1),X0)) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK4(k6_relat_1(X1),X2),sK5(k6_relat_1(X1),X2)),k6_relat_1(X1)) | r1_tarski(k6_relat_1(X1),X2)) )),
% 0.21/0.47    inference(resolution,[],[f31,f29])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~r2_hidden(sK4(k6_relat_1(sK2),sK3),sK2)),
% 0.21/0.47    inference(resolution,[],[f94,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK3) | ~r2_hidden(X2,sK2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r1_tarski(k6_relat_1(sK2),sK3) & ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK3) | ~r2_hidden(X2,sK2)) & v1_relat_1(sK3)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) & ! [X2] : (r2_hidden(k4_tarski(X2,X2),X1) | ~r2_hidden(X2,X0)) & v1_relat_1(X1)) => (~r1_tarski(k6_relat_1(sK2),sK3) & ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK3) | ~r2_hidden(X2,sK2)) & v1_relat_1(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) & ! [X2] : (r2_hidden(k4_tarski(X2,X2),X1) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : ((~r1_tarski(k6_relat_1(X0),X1) & ! [X2] : (r2_hidden(k4_tarski(X2,X2),X1) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ~r2_hidden(k4_tarski(sK4(k6_relat_1(sK2),sK3),sK4(k6_relat_1(sK2),sK3)),sK3)),
% 0.21/0.47    inference(global_subsumption,[],[f28,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~r2_hidden(k4_tarski(sK4(k6_relat_1(sK2),sK3),sK4(k6_relat_1(sK2),sK3)),sK3) | r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.47    inference(superposition,[],[f67,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    sK4(k6_relat_1(sK2),sK3) = sK5(k6_relat_1(sK2),sK3)),
% 0.21/0.47    inference(resolution,[],[f84,f28])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X4,X5] : (r1_tarski(k6_relat_1(X4),X5) | sK4(k6_relat_1(X4),X5) = sK5(k6_relat_1(X4),X5)) )),
% 0.21/0.47    inference(resolution,[],[f64,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) | X0 = X1) )),
% 0.21/0.47    inference(resolution,[],[f45,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (sP8(k6_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f44,f51])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sP0(X0,X1) | sP8(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44_D])).
% 0.21/0.47  fof(f44_D,plain,(
% 0.21/0.47    ( ! [X1] : (( ! [X0] : ~sP0(X0,X1) ) <=> ~sP8(X1)) )),
% 0.21/0.47    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X4,X5,X1] : (~sP8(X1) | ~r2_hidden(k4_tarski(X4,X5),X1) | X4 = X5) )),
% 0.21/0.47    inference(general_splitting,[],[f36,f44_D])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r2_hidden(k4_tarski(sK4(k6_relat_1(X1),X2),sK5(k6_relat_1(X1),X2)),X2) | r1_tarski(k6_relat_1(X1),X2)) )),
% 0.21/0.47    inference(resolution,[],[f32,f29])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25530)------------------------------
% 0.21/0.47  % (25530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25530)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25530)Memory used [KB]: 6268
% 0.21/0.47  % (25530)Time elapsed: 0.059 s
% 0.21/0.47  % (25530)------------------------------
% 0.21/0.47  % (25530)------------------------------
% 0.21/0.47  % (25517)Success in time 0.111 s
%------------------------------------------------------------------------------
