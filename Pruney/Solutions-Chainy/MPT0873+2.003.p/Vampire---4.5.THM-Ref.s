%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 583 expanded)
%              Number of leaves         :   21 ( 159 expanded)
%              Depth                    :   19
%              Number of atoms          :  225 (1574 expanded)
%              Number of equality atoms :  138 (1376 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f113,f170,f208,f246,f255,f259])).

fof(f259,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl10_8 ),
    inference(resolution,[],[f169,f238])).

fof(f238,plain,(
    ! [X0] : r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tarski(X0,X0))
      | r2_hidden(X0,k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f227,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f227,plain,(
    ! [X1] : ~ r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(backward_demodulation,[],[f66,f220])).

fof(f220,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X1) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f48,f36,f47,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f32,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f49,f36,f47,f50])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(f66,plain,(
    ! [X1] : ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f38,f51,f51])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f169,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,sK1),X0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_8
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f255,plain,(
    ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl10_9 ),
    inference(resolution,[],[f207,f238])).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_9
  <=> ! [X0] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f246,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(resolution,[],[f238,f159])).

fof(f159,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f155,f139])).

fof(f139,plain,
    ( ! [X12,X13] : ~ r2_hidden(k4_tarski(X12,sK1),k2_zfmisc_1(X13,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | spl10_2 ),
    inference(extensionality_resolution,[],[f60,f75])).

fof(f75,plain,
    ( sK1 != sK5
    | spl10_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl10_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f155,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f67,f120])).

fof(f120,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK5)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f104,f70])).

fof(f70,plain,
    ( sK0 = sK4
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f104,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    inference(forward_demodulation,[],[f101,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK8(X0,X1) != X1
              & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK8(X0,X1) != X1
        & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f101,plain,(
    k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(superposition,[],[f88,f99])).

fof(f99,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    inference(forward_demodulation,[],[f98,f88])).

fof(f98,plain,(
    k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(superposition,[],[f88,f55])).

fof(f55,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f30,f43,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f30,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f208,plain,
    ( spl10_9
    | spl10_4 ),
    inference(avatar_split_clause,[],[f204,f81,f206])).

fof(f81,plain,
    ( spl10_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f204,plain,(
    ! [X0] :
      ( sK3 = sK7
      | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0) ) ),
    inference(resolution,[],[f145,f67])).

fof(f145,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))
      | sK7 = X5 ) ),
    inference(superposition,[],[f60,f100])).

fof(f100,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK7) ),
    inference(backward_demodulation,[],[f55,f99])).

fof(f170,plain,
    ( spl10_8
    | spl10_3 ),
    inference(avatar_split_clause,[],[f166,f77,f168])).

% (14015)Refutation not found, incomplete strategy% (14015)------------------------------
% (14015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f77,plain,
    ( spl10_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

% (14015)Termination reason: Refutation not found, incomplete strategy

fof(f166,plain,(
    ! [X0] :
      ( sK2 = sK6
      | ~ r2_hidden(k4_tarski(sK0,sK1),X0) ) ),
    inference(resolution,[],[f144,f67])).

% (14015)Memory used [KB]: 1663
% (14015)Time elapsed: 0.148 s
% (14015)------------------------------
% (14015)------------------------------
fof(f144,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | sK6 = X3 ) ),
    inference(superposition,[],[f60,f107])).

fof(f107,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK6) ),
    inference(backward_demodulation,[],[f99,f104])).

fof(f113,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f111,f71])).

fof(f71,plain,
    ( sK0 != sK4
    | spl10_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f111,plain,(
    sK0 = sK4 ),
    inference(forward_demodulation,[],[f108,f88])).

fof(f108,plain,(
    sK4 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f88,f104])).

fof(f84,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f31,f81,f77,f73,f69])).

fof(f31,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (14000)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.49  % (14020)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.50  % (14012)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (14024)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (14016)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (14008)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (14005)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (14002)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (14009)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (14006)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14019)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (14028)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (14003)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (14010)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (14001)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (14030)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (14027)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (14030)Refutation not found, incomplete strategy% (14030)------------------------------
% 0.20/0.54  % (14030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14030)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14030)Memory used [KB]: 1663
% 0.20/0.54  % (14030)Time elapsed: 0.001 s
% 0.20/0.54  % (14030)------------------------------
% 0.20/0.54  % (14030)------------------------------
% 0.20/0.54  % (14001)Refutation not found, incomplete strategy% (14001)------------------------------
% 0.20/0.54  % (14001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14001)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14001)Memory used [KB]: 1663
% 0.20/0.54  % (14001)Time elapsed: 0.125 s
% 0.20/0.54  % (14001)------------------------------
% 0.20/0.54  % (14001)------------------------------
% 0.20/0.54  % (14017)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (14027)Refutation not found, incomplete strategy% (14027)------------------------------
% 0.20/0.54  % (14027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14027)Memory used [KB]: 6268
% 0.20/0.54  % (14027)Time elapsed: 0.129 s
% 0.20/0.54  % (14027)------------------------------
% 0.20/0.54  % (14027)------------------------------
% 0.20/0.54  % (14004)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (14015)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (14022)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (14029)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (14014)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (14011)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (14025)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (14021)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (14013)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (14019)Refutation not found, incomplete strategy% (14019)------------------------------
% 0.20/0.55  % (14019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14019)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14019)Memory used [KB]: 1663
% 0.20/0.55  % (14019)Time elapsed: 0.142 s
% 0.20/0.55  % (14019)------------------------------
% 0.20/0.55  % (14019)------------------------------
% 0.20/0.55  % (14023)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (14017)Refutation not found, incomplete strategy% (14017)------------------------------
% 0.20/0.55  % (14017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14017)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14017)Memory used [KB]: 10618
% 0.20/0.55  % (14017)Time elapsed: 0.137 s
% 0.20/0.55  % (14017)------------------------------
% 0.20/0.55  % (14017)------------------------------
% 0.20/0.55  % (14026)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (14013)Refutation not found, incomplete strategy% (14013)------------------------------
% 0.20/0.55  % (14013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14013)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14013)Memory used [KB]: 10618
% 0.20/0.55  % (14013)Time elapsed: 0.140 s
% 0.20/0.55  % (14013)------------------------------
% 0.20/0.55  % (14013)------------------------------
% 0.20/0.55  % (14006)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f84,f113,f170,f208,f246,f255,f259])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    ~spl10_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f258])).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    $false | ~spl10_8),
% 0.20/0.55    inference(resolution,[],[f169,f238])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,k2_tarski(X0,X0))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f237])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,k2_tarski(X0,X0)) | r2_hidden(X0,k2_tarski(X0,X0))) )),
% 0.20/0.55    inference(resolution,[],[f227,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f66,f220])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X1)) )),
% 0.20/0.55    inference(superposition,[],[f54,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f37,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f48,f36,f47,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f32,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f39,f47])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f49,f36,f47,f50])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f38,f51,f51])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK1),X0)) ) | ~spl10_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f168])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    spl10_8 <=> ! [X0] : ~r2_hidden(k4_tarski(sK0,sK1),X0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    ~spl10_9),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f254])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    $false | ~spl10_9),
% 0.20/0.55    inference(resolution,[],[f207,f238])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0)) ) | ~spl10_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f206])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    spl10_9 <=> ! [X0] : ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    ~spl10_1 | spl10_2),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f245])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    $false | (~spl10_1 | spl10_2)),
% 0.20/0.55    inference(resolution,[],[f238,f159])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | (~spl10_1 | spl10_2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f155,f139])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    ( ! [X12,X13] : (~r2_hidden(k4_tarski(X12,sK1),k2_zfmisc_1(X13,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ) | spl10_2),
% 0.20/0.55    inference(extensionality_resolution,[],[f60,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    sK1 != sK5 | spl10_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    spl10_2 <=> sK1 = sK5),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 = X3) )),
% 0.20/0.55    inference(definition_unfolding,[],[f45,f51])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.20/0.55    inference(flattening,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.20/0.55    inference(nnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | ~r2_hidden(sK0,X0)) ) | ~spl10_1),
% 0.20/0.55    inference(superposition,[],[f67,f120])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    k4_tarski(sK0,sK1) = k4_tarski(sK0,sK5) | ~spl10_1),
% 0.20/0.55    inference(backward_demodulation,[],[f104,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    sK0 = sK4 | ~spl10_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    spl10_1 <=> sK0 = sK4),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.20/0.55    inference(forward_demodulation,[],[f101,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.55    inference(equality_resolution,[],[f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k1_mcart_1(k4_tarski(X4,X5)) = X4) )),
% 0.20/0.55    inference(equality_resolution,[],[f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.20/0.55    inference(equality_resolution,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK8(X0,X1) != X1 & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f25,f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK8(X0,X1) != X1 & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.55    inference(rectify,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.55    inference(nnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 0.20/0.55    inference(rectify,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.20/0.55    inference(superposition,[],[f88,f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.20/0.55    inference(forward_demodulation,[],[f98,f88])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.20/0.55    inference(superposition,[],[f88,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.20/0.55    inference(definition_unfolding,[],[f30,f43,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.55    inference(negated_conjecture,[],[f14])).
% 0.20/0.55  fof(f14,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(equality_resolution,[],[f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f46,f51])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    spl10_9 | spl10_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f204,f81,f206])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl10_4 <=> sK3 = sK7),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ( ! [X0] : (sK3 = sK7 | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0)) )),
% 0.20/0.55    inference(resolution,[],[f145,f67])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ( ! [X4,X5] : (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) | sK7 = X5) )),
% 0.20/0.55    inference(superposition,[],[f60,f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK7)),
% 0.20/0.55    inference(backward_demodulation,[],[f55,f99])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    spl10_8 | spl10_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f166,f77,f168])).
% 0.20/0.55  % (14015)Refutation not found, incomplete strategy% (14015)------------------------------
% 0.20/0.55  % (14015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl10_3 <=> sK2 = sK6),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.55  % (14015)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    ( ! [X0] : (sK2 = sK6 | ~r2_hidden(k4_tarski(sK0,sK1),X0)) )),
% 0.20/0.55    inference(resolution,[],[f144,f67])).
% 0.20/0.55  % (14015)Memory used [KB]: 1663
% 0.20/0.55  % (14015)Time elapsed: 0.148 s
% 0.20/0.55  % (14015)------------------------------
% 0.20/0.55  % (14015)------------------------------
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | sK6 = X3) )),
% 0.20/0.55    inference(superposition,[],[f60,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK6)),
% 0.20/0.55    inference(backward_demodulation,[],[f99,f104])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl10_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    $false | spl10_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f111,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    sK0 != sK4 | spl10_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f69])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    sK0 = sK4),
% 0.20/0.55    inference(forward_demodulation,[],[f108,f88])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    sK4 = k1_mcart_1(k4_tarski(sK0,sK1))),
% 0.20/0.55    inference(superposition,[],[f88,f104])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f31,f81,f77,f73,f69])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (14006)------------------------------
% 0.20/0.55  % (14006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14006)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (14006)Memory used [KB]: 10874
% 0.20/0.55  % (14006)Time elapsed: 0.120 s
% 0.20/0.55  % (14006)------------------------------
% 0.20/0.55  % (14006)------------------------------
% 0.20/0.55  % (13997)Success in time 0.191 s
%------------------------------------------------------------------------------
