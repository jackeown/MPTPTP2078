%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 201 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  260 ( 744 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f104,f113,f166,f169,f204,f217])).

fof(f217,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f212,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f212,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_enumset1(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),X1),k1_xboole_0)
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f103,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_5
  <=> r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f204,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f198,f177])).

fof(f177,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f171,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f171,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f76,f29])).

fof(f29,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

% (3985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f76,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_1
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f198,plain,
    ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f178,f51])).

fof(f51,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f178,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f171,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,
    ( ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f167,f28])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f112,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k3_tarski(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_4
  <=> k1_xboole_0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f112,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_7
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f166,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f160,f133])).

fof(f133,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f127,f34])).

fof(f127,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f125,f29])).

fof(f125,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f119,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,
    ( r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f108,f34])).

fof(f108,plain,
    ( ~ r1_xboole_0(sK2(sK0,sK0),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_6
  <=> r1_xboole_0(sK2(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f160,plain,
    ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f134,f51])).

fof(f134,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | spl6_6 ),
    inference(resolution,[],[f127,f33])).

fof(f113,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f89,f78,f110,f106])).

fof(f78,plain,
    ( spl6_2
  <=> ! [X7] :
        ( k3_tarski(sK0) = X7
        | r2_hidden(sK2(sK0,X7),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f89,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ r1_xboole_0(sK2(sK0,sK0),sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f29])).

fof(f79,plain,
    ( ! [X7] :
        ( r2_hidden(sK2(sK0,X7),X7)
        | k3_tarski(sK0) = X7 )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f104,plain,
    ( spl6_5
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f86,f78,f96,f101])).

fof(f86,plain,
    ( k1_xboole_0 = k3_tarski(sK0)
    | r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(superposition,[],[f49,f30])).

fof(f30,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k3_tarski(X0))
      | r2_hidden(sK4(X0,X5),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f80,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f72,f78,f74])).

fof(f72,plain,(
    ! [X7] :
      ( k3_tarski(sK0) = X7
      | r2_hidden(sK2(sK0,X7),X7)
      | r2_hidden(sK5(sK0),sK0) ) ),
    inference(resolution,[],[f66,f42])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK3(sK0,X0),sK0),sK0)
      | k3_tarski(sK0) = X0
      | r2_hidden(sK2(sK0,X0),X0) ) ),
    inference(resolution,[],[f62,f34])).

fof(f62,plain,(
    ! [X17] :
      ( ~ r1_xboole_0(sK3(sK0,X17),sK0)
      | r2_hidden(sK2(sK0,X17),X17)
      | k3_tarski(sK0) = X17 ) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (3987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (3978)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (3971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (3970)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (3969)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (3968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (3965)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (3993)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (3976)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3967)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3968)Refutation not found, incomplete strategy% (3968)------------------------------
% 0.21/0.53  % (3968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3968)Memory used [KB]: 6140
% 0.21/0.53  % (3968)Time elapsed: 0.128 s
% 0.21/0.53  % (3968)------------------------------
% 0.21/0.53  % (3968)------------------------------
% 0.21/0.53  % (3967)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f80,f104,f113,f166,f169,f204,f217])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ~spl6_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    $false | ~spl6_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f212,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_xboole_0(k2_enumset1(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),X1),k1_xboole_0)) ) | ~spl6_5),
% 0.21/0.53    inference(resolution,[],[f103,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl6_5 <=> r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ~spl6_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    $false | ~spl6_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f198,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~spl6_1),
% 0.21/0.53    inference(resolution,[],[f171,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_1),
% 0.21/0.53    inference(resolution,[],[f76,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.53  % (3985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    r2_hidden(sK5(sK0),sK0) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl6_1 <=> r2_hidden(sK5(sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~spl6_1),
% 0.21/0.53    inference(resolution,[],[f178,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.53    inference(condensation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | ~spl6_1),
% 0.21/0.53    inference(resolution,[],[f171,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ~spl6_4 | ~spl6_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    $false | (~spl6_4 | ~spl6_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | (~spl6_4 | ~spl6_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f112,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    k1_xboole_0 = k3_tarski(sK0) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl6_4 <=> k1_xboole_0 = k3_tarski(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    sK0 = k3_tarski(sK0) | ~spl6_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl6_7 <=> sK0 = k3_tarski(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl6_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    $false | spl6_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f160,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f127,f34])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~r1_xboole_0(sK5(sK0),sK0) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f125,f29])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r2_hidden(sK5(sK0),sK0) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f119,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f108,f34])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~r1_xboole_0(sK2(sK0,sK0),sK0) | spl6_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl6_6 <=> r1_xboole_0(sK2(sK0,sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ~r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f134,f51])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | spl6_6),
% 0.21/0.53    inference(resolution,[],[f127,f33])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ~spl6_6 | spl6_7 | ~spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f89,f78,f110,f106])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl6_2 <=> ! [X7] : (k3_tarski(sK0) = X7 | r2_hidden(sK2(sK0,X7),X7))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    sK0 = k3_tarski(sK0) | ~r1_xboole_0(sK2(sK0,sK0),sK0) | ~spl6_2),
% 0.21/0.53    inference(resolution,[],[f79,f29])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X7] : (r2_hidden(sK2(sK0,X7),X7) | k3_tarski(sK0) = X7) ) | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f78])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl6_5 | spl6_4 | ~spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f86,f78,f96,f101])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    k1_xboole_0 = k3_tarski(sK0) | r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_2),
% 0.21/0.53    inference(resolution,[],[f79,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f49,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X5] : (~r2_hidden(X5,k3_tarski(X0)) | r2_hidden(sK4(X0,X5),X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl6_1 | spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f72,f78,f74])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X7] : (k3_tarski(sK0) = X7 | r2_hidden(sK2(sK0,X7),X7) | r2_hidden(sK5(sK0),sK0)) )),
% 0.21/0.53    inference(resolution,[],[f66,f42])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK1(sK3(sK0,X0),sK0),sK0) | k3_tarski(sK0) = X0 | r2_hidden(sK2(sK0,X0),X0)) )),
% 0.21/0.53    inference(resolution,[],[f62,f34])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X17] : (~r1_xboole_0(sK3(sK0,X17),sK0) | r2_hidden(sK2(sK0,X17),X17) | k3_tarski(sK0) = X17) )),
% 0.21/0.53    inference(resolution,[],[f40,f29])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3967)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3967)Memory used [KB]: 10746
% 0.21/0.53  % (3967)Time elapsed: 0.130 s
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3985)Refutation not found, incomplete strategy% (3985)------------------------------
% 0.21/0.53  % (3985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3985)Memory used [KB]: 1663
% 0.21/0.53  % (3985)Time elapsed: 0.131 s
% 0.21/0.53  % (3985)------------------------------
% 0.21/0.53  % (3985)------------------------------
% 0.21/0.54  % (3986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3966)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3964)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3975)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3964)Refutation not found, incomplete strategy% (3964)------------------------------
% 0.21/0.54  % (3964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3964)Memory used [KB]: 1663
% 0.21/0.54  % (3964)Time elapsed: 0.126 s
% 0.21/0.54  % (3964)------------------------------
% 0.21/0.54  % (3964)------------------------------
% 0.21/0.54  % (3977)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (3963)Success in time 0.177 s
%------------------------------------------------------------------------------
