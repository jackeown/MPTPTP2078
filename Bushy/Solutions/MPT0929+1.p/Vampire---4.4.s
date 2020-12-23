%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t89_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 100 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 263 expanded)
%              Number of equality atoms :   86 ( 224 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f76,f78,f85,f87,f89])).

fof(f89,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k2_mcart_1(k4_tarski(X1,X2)) = X5 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X5
      | k2_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X5
      | k2_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d2_mcart_1)).

fof(f83,plain,
    ( k2_mcart_1(k4_tarski(sK0,sK1)) != sK1
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f80,f58])).

fof(f58,plain,
    ( k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK1
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl10_5
  <=> k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f80,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k1_mcart_1(k4_tarski(X1,X2)) = X4 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X4
      | k1_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X4
      | k1_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d1_mcart_1)).

fof(f87,plain,(
    spl10_7 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f82,f80])).

fof(f82,plain,
    ( k1_mcart_1(k4_tarski(sK0,sK1)) != sK0
    | ~ spl10_7 ),
    inference(backward_demodulation,[],[f80,f64])).

fof(f64,plain,
    ( k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK0
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_7
  <=> k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f85,plain,(
    spl10_9 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f75,f80])).

fof(f75,plain,
    ( k1_mcart_1(k4_tarski(sK3,sK4)) != sK3
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl10_9
  <=> k1_mcart_1(k4_tarski(sK3,sK4)) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f78,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f68,f66])).

fof(f68,plain,
    ( k2_mcart_1(k4_tarski(sK3,sK4)) != sK4
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f66,f46])).

fof(f46,plain,
    ( k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK4
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl10_1
  <=> k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f76,plain,
    ( ~ spl10_9
    | spl10_3 ),
    inference(avatar_split_clause,[],[f67,f51,f74])).

fof(f51,plain,
    ( spl10_3
  <=> k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f67,plain,
    ( k1_mcart_1(k4_tarski(sK3,sK4)) != sK3
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f66,f52])).

fof(f52,plain,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK3
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f32,f63,f57,f51,f45])).

fof(f32,plain,
    ( k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) != sK1
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK3
    | k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) != sK4 ),
    inference(definition_unfolding,[],[f21,f25,f24,f23,f22])).

fof(f22,plain,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d17_mcart_1)).

fof(f23,plain,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d16_mcart_1)).

fof(f24,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d15_mcart_1)).

fof(f25,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',d14_mcart_1)).

fof(f21,plain,
    ( k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) != sK0
    | k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) != sK1
    | k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) != sK3
    | k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) != sK4 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t89_mcart_1.p',t89_mcart_1)).
%------------------------------------------------------------------------------
