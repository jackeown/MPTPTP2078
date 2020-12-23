%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:09 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 154 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 ( 481 expanded)
%              Number of equality atoms :   53 (  95 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f137,f189])).

fof(f189,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f184,f148])).

fof(f148,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f107,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),sK0) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f107,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_1
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f184,plain,
    ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f149,f72])).

fof(f72,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f149,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f107,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),X0) ) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f132,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(resolution,[],[f131,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | sK0 = X0 )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | sK0 = X0
        | sK0 = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f122,f114])).

fof(f114,plain,
    ( ! [X4] :
        ( r2_hidden(sK2(X4),X4)
        | sK0 = X4 )
    | ~ spl4_2 ),
    inference(resolution,[],[f110,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( ! [X7] :
        ( r2_hidden(sK3(X7,X7,sK0),X7)
        | sK0 = X7 )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_2
  <=> ! [X7] :
        ( r2_hidden(sK3(X7,X7,sK0),X7)
        | sK0 = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f122,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK2(X2),X3)
        | ~ r1_xboole_0(X3,X2)
        | sK0 = X2 )
    | ~ spl4_2 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f111,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,(
    ! [X7] :
      ( r2_hidden(sK3(X7,X7,sK0),X7)
      | sK0 = X7
      | r2_hidden(sK2(sK0),sK0) ) ),
    inference(resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK3(X0,X0,sK0),sK0),sK0)
      | r2_hidden(sK3(X0,X0,sK0),X0)
      | sK0 = X0 ) ),
    inference(superposition,[],[f83,f62])).

fof(f62,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f83,plain,(
    ! [X19,X20] :
      ( sK0 = k1_setfam_1(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20))
      | r2_hidden(sK3(X19,X20,sK0),X20)
      | r2_hidden(sK1(sK3(X19,X20,sK0),sK0),sK0) ) ),
    inference(resolution,[],[f64,f75])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (6941)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.47  % (6933)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.48  % (6934)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.49  % (6926)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (6926)Refutation not found, incomplete strategy% (6926)------------------------------
% 0.19/0.50  % (6926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (6926)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (6926)Memory used [KB]: 1791
% 0.19/0.50  % (6926)Time elapsed: 0.103 s
% 0.19/0.50  % (6926)------------------------------
% 0.19/0.50  % (6926)------------------------------
% 0.19/0.50  % (6935)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (6929)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (6948)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (6948)Refutation not found, incomplete strategy% (6948)------------------------------
% 0.19/0.51  % (6948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6948)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (6948)Memory used [KB]: 10618
% 0.19/0.51  % (6948)Time elapsed: 0.089 s
% 0.19/0.51  % (6948)------------------------------
% 0.19/0.51  % (6948)------------------------------
% 0.19/0.51  % (6945)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (6940)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (6930)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.52  % (6927)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.52  % (6946)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.52  % (6929)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f190,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(avatar_sat_refutation,[],[f111,f137,f189])).
% 1.31/0.52  fof(f189,plain,(
% 1.31/0.52    ~spl4_1),
% 1.31/0.52    inference(avatar_contradiction_clause,[],[f188])).
% 1.31/0.52  fof(f188,plain,(
% 1.31/0.52    $false | ~spl4_1),
% 1.31/0.52    inference(subsumption_resolution,[],[f184,f148])).
% 1.31/0.52  fof(f148,plain,(
% 1.31/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~spl4_1),
% 1.31/0.52    inference(resolution,[],[f107,f75])).
% 1.31/0.52  fof(f75,plain,(
% 1.31/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),sK0)) )),
% 1.31/0.52    inference(resolution,[],[f40,f34])).
% 1.31/0.52  fof(f34,plain,(
% 1.31/0.52    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f23])).
% 1.31/0.52  fof(f23,plain,(
% 1.31/0.52    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 1.31/0.52  fof(f22,plain,(
% 1.31/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f18,plain,(
% 1.31/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.31/0.52    inference(ennf_transformation,[],[f15])).
% 1.31/0.52  fof(f15,negated_conjecture,(
% 1.31/0.52    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.31/0.52    inference(negated_conjecture,[],[f14])).
% 1.31/0.52  fof(f14,conjecture,(
% 1.31/0.52    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 1.31/0.52  fof(f40,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f25])).
% 1.31/0.52  fof(f25,plain,(
% 1.31/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).
% 1.31/0.52  fof(f24,plain,(
% 1.31/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f19,plain,(
% 1.31/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(ennf_transformation,[],[f17])).
% 1.31/0.52  fof(f17,plain,(
% 1.31/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(rectify,[],[f4])).
% 1.31/0.52  fof(f4,axiom,(
% 1.31/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.31/0.52  fof(f107,plain,(
% 1.31/0.52    r2_hidden(sK2(sK0),sK0) | ~spl4_1),
% 1.31/0.52    inference(avatar_component_clause,[],[f105])).
% 1.31/0.52  fof(f105,plain,(
% 1.31/0.52    spl4_1 <=> r2_hidden(sK2(sK0),sK0)),
% 1.31/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.31/0.52  fof(f184,plain,(
% 1.31/0.52    ~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~spl4_1),
% 1.31/0.52    inference(resolution,[],[f149,f72])).
% 1.31/0.52  fof(f72,plain,(
% 1.31/0.52    ( ! [X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) )),
% 1.31/0.52    inference(condensation,[],[f44])).
% 1.31/0.52  fof(f44,plain,(
% 1.31/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f27])).
% 1.31/0.52  fof(f27,plain,(
% 1.31/0.52    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f12])).
% 1.31/0.53  fof(f12,axiom,(
% 1.31/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 1.31/0.53  fof(f149,plain,(
% 1.31/0.53    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl4_1),
% 1.31/0.53    inference(resolution,[],[f107,f74])).
% 1.31/0.53  fof(f74,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),X0)) )),
% 1.31/0.53    inference(resolution,[],[f39,f34])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f137,plain,(
% 1.31/0.53    ~spl4_2),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f136])).
% 1.31/0.53  fof(f136,plain,(
% 1.31/0.53    $false | ~spl4_2),
% 1.31/0.53    inference(subsumption_resolution,[],[f132,f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    k1_xboole_0 != sK0),
% 1.31/0.53    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  fof(f132,plain,(
% 1.31/0.53    k1_xboole_0 = sK0 | ~spl4_2),
% 1.31/0.53    inference(resolution,[],[f131,f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.31/0.53  fof(f131,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | sK0 = X0) ) | ~spl4_2),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f130])).
% 1.31/0.53  fof(f130,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | sK0 = X0 | sK0 = X0) ) | ~spl4_2),
% 1.31/0.53    inference(resolution,[],[f122,f114])).
% 1.31/0.53  fof(f114,plain,(
% 1.31/0.53    ( ! [X4] : (r2_hidden(sK2(X4),X4) | sK0 = X4) ) | ~spl4_2),
% 1.31/0.53    inference(resolution,[],[f110,f43])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f110,plain,(
% 1.31/0.53    ( ! [X7] : (r2_hidden(sK3(X7,X7,sK0),X7) | sK0 = X7) ) | ~spl4_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f109])).
% 1.31/0.53  fof(f109,plain,(
% 1.31/0.53    spl4_2 <=> ! [X7] : (r2_hidden(sK3(X7,X7,sK0),X7) | sK0 = X7)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.31/0.53  fof(f122,plain,(
% 1.31/0.53    ( ! [X2,X3] : (~r2_hidden(sK2(X2),X3) | ~r1_xboole_0(X3,X2) | sK0 = X2) ) | ~spl4_2),
% 1.31/0.53    inference(resolution,[],[f114,f41])).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f111,plain,(
% 1.31/0.53    spl4_1 | spl4_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f103,f109,f105])).
% 1.31/0.53  fof(f103,plain,(
% 1.31/0.53    ( ! [X7] : (r2_hidden(sK3(X7,X7,sK0),X7) | sK0 = X7 | r2_hidden(sK2(sK0),sK0)) )),
% 1.31/0.53    inference(resolution,[],[f94,f43])).
% 1.31/0.53  fof(f94,plain,(
% 1.31/0.53    ( ! [X0] : (r2_hidden(sK1(sK3(X0,X0,sK0),sK0),sK0) | r2_hidden(sK3(X0,X0,sK0),X0) | sK0 = X0) )),
% 1.31/0.53    inference(superposition,[],[f83,f62])).
% 1.31/0.53  fof(f62,plain,(
% 1.31/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.31/0.53    inference(definition_unfolding,[],[f36,f61])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.31/0.53    inference(definition_unfolding,[],[f37,f60])).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f38,f59])).
% 1.31/0.53  fof(f59,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f45,f58])).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f52,f57])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f53,f56])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f54,f55])).
% 1.31/0.53  fof(f55,plain,(
% 1.31/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.31/0.53  fof(f54,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.53  fof(f53,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f6])).
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,axiom,(
% 1.31/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.31/0.53    inference(rectify,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.31/0.53  fof(f83,plain,(
% 1.31/0.53    ( ! [X19,X20] : (sK0 = k1_setfam_1(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) | r2_hidden(sK3(X19,X20,sK0),X20) | r2_hidden(sK1(sK3(X19,X20,sK0),sK0),sK0)) )),
% 1.31/0.53    inference(resolution,[],[f64,f75])).
% 1.31/0.53  fof(f64,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2) )),
% 1.31/0.53    inference(definition_unfolding,[],[f50,f61])).
% 1.31/0.53  fof(f50,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.53    inference(rectify,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.53    inference(flattening,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.53    inference(nnf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (6929)------------------------------
% 1.31/0.53  % (6929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (6929)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (6929)Memory used [KB]: 10746
% 1.31/0.53  % (6929)Time elapsed: 0.132 s
% 1.31/0.53  % (6929)------------------------------
% 1.31/0.53  % (6929)------------------------------
% 1.31/0.53  % (6953)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.53  % (6935)Refutation not found, incomplete strategy% (6935)------------------------------
% 1.31/0.53  % (6935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (6935)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (6935)Memory used [KB]: 10746
% 1.31/0.53  % (6935)Time elapsed: 0.137 s
% 1.31/0.53  % (6935)------------------------------
% 1.31/0.53  % (6935)------------------------------
% 1.31/0.53  % (6931)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (6954)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.53  % (6951)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.53  % (6925)Success in time 0.18 s
%------------------------------------------------------------------------------
