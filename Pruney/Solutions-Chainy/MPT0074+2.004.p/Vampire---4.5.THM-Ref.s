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
% DateTime   : Thu Dec  3 12:30:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 142 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  276 ( 516 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f72,f153,f158,f182,f196])).

fof(f196,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl8_3 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_3 ),
    inference(superposition,[],[f39,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != sK1
    & r1_xboole_0(sK2,sK3)
    & r1_tarski(sK1,sK3)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK1
      & r1_xboole_0(sK2,sK3)
      & r1_tarski(sK1,sK3)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

% (10629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f182,plain,
    ( ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(resolution,[],[f179,f152])).

fof(f152,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_4
  <=> r2_hidden(sK5(sK1,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f179,plain,
    ( ~ r2_hidden(sK5(sK1,k1_xboole_0),sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f162,f77])).

fof(f77,plain,(
    sP0(sK3,sK2,sK2) ),
    inference(superposition,[],[f59,f76])).

fof(f76,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f74,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f41,f61])).

fof(f61,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK3,X1,X0)
        | ~ r2_hidden(sK5(sK1,k1_xboole_0),X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f157,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f157,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_5
  <=> r2_hidden(sK5(sK1,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f158,plain,
    ( spl8_3
    | spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f143,f68,f155,f146])).

fof(f68,plain,
    ( spl8_2
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f143,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK3)
    | k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(resolution,[],[f141,f37])).

fof(f37,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | r2_hidden(sK5(X8,k1_xboole_0),X9)
        | k1_xboole_0 = X8 )
    | ~ spl8_2 ),
    inference(resolution,[],[f132,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

% (10636)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f132,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(X3,k1_xboole_0),X3)
        | k1_xboole_0 = X3 )
    | ~ spl8_2 ),
    inference(resolution,[],[f44,f69])).

fof(f69,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f153,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f142,f68,f150,f146])).

fof(f142,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK2)
    | k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(resolution,[],[f141,f36])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl8_1
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f70,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f68,f64])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(sK2,sK3) ) ),
    inference(superposition,[],[f43,f61])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

% (10649)Refutation not found, incomplete strategy% (10649)------------------------------
% (10649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10649)Termination reason: Refutation not found, incomplete strategy

% (10649)Memory used [KB]: 10618
% (10649)Time elapsed: 0.080 s
% (10649)------------------------------
% (10649)------------------------------
fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (10650)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (10642)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (10639)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10644)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (10639)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (10640)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (10649)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (10627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (10655)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.53  % (10641)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.53  % (10631)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f197,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f70,f72,f153,f158,f182,f196])).
% 1.30/0.53  fof(f196,plain,(
% 1.30/0.53    ~spl8_3),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f195])).
% 1.30/0.53  fof(f195,plain,(
% 1.30/0.53    $false | ~spl8_3),
% 1.30/0.53    inference(trivial_inequality_removal,[],[f194])).
% 1.30/0.53  fof(f194,plain,(
% 1.30/0.53    k1_xboole_0 != k1_xboole_0 | ~spl8_3),
% 1.30/0.53    inference(superposition,[],[f39,f148])).
% 1.30/0.53  fof(f148,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | ~spl8_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f146])).
% 1.30/0.53  fof(f146,plain,(
% 1.30/0.53    spl8_3 <=> k1_xboole_0 = sK1),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    k1_xboole_0 != sK1),
% 1.30/0.53    inference(cnf_transformation,[],[f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    k1_xboole_0 != sK1 & r1_xboole_0(sK2,sK3) & r1_tarski(sK1,sK3) & r1_tarski(sK1,sK2)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK1 & r1_xboole_0(sK2,sK3) & r1_tarski(sK1,sK3) & r1_tarski(sK1,sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 1.30/0.53    inference(flattening,[],[f11])).
% 1.30/0.53  % (10629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  fof(f11,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.30/0.53    inference(negated_conjecture,[],[f8])).
% 1.30/0.53  fof(f8,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.30/0.53  fof(f182,plain,(
% 1.30/0.53    ~spl8_4 | ~spl8_5),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f181])).
% 1.30/0.53  fof(f181,plain,(
% 1.30/0.53    $false | (~spl8_4 | ~spl8_5)),
% 1.30/0.53    inference(resolution,[],[f179,f152])).
% 1.30/0.53  fof(f152,plain,(
% 1.30/0.53    r2_hidden(sK5(sK1,k1_xboole_0),sK2) | ~spl8_4),
% 1.30/0.53    inference(avatar_component_clause,[],[f150])).
% 1.30/0.53  fof(f150,plain,(
% 1.30/0.53    spl8_4 <=> r2_hidden(sK5(sK1,k1_xboole_0),sK2)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.30/0.53  fof(f179,plain,(
% 1.30/0.53    ~r2_hidden(sK5(sK1,k1_xboole_0),sK2) | ~spl8_5),
% 1.30/0.53    inference(resolution,[],[f162,f77])).
% 1.30/0.53  fof(f77,plain,(
% 1.30/0.53    sP0(sK3,sK2,sK2)),
% 1.30/0.53    inference(superposition,[],[f59,f76])).
% 1.30/0.53  fof(f76,plain,(
% 1.30/0.53    sK2 = k4_xboole_0(sK2,sK3)),
% 1.30/0.53    inference(forward_demodulation,[],[f74,f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.53    inference(cnf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.30/0.53  fof(f74,plain,(
% 1.30/0.53    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.30/0.53    inference(superposition,[],[f41,f61])).
% 1.30/0.53  fof(f61,plain,(
% 1.30/0.53    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 1.30/0.53    inference(resolution,[],[f49,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    r1_xboole_0(sK2,sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f19])).
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(nnf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.30/0.53  fof(f59,plain,(
% 1.30/0.53    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.30/0.53    inference(equality_resolution,[],[f57])).
% 1.30/0.53  fof(f57,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.30/0.53    inference(cnf_transformation,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.30/0.53    inference(nnf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.30/0.53    inference(definition_folding,[],[f2,f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.30/0.53  fof(f162,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~sP0(sK3,X1,X0) | ~r2_hidden(sK5(sK1,k1_xboole_0),X0)) ) | ~spl8_5),
% 1.30/0.53    inference(resolution,[],[f157,f52])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.30/0.53    inference(rectify,[],[f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.30/0.53    inference(flattening,[],[f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.30/0.53    inference(nnf_transformation,[],[f16])).
% 1.30/0.53  fof(f157,plain,(
% 1.30/0.53    r2_hidden(sK5(sK1,k1_xboole_0),sK3) | ~spl8_5),
% 1.30/0.53    inference(avatar_component_clause,[],[f155])).
% 1.30/0.53  fof(f155,plain,(
% 1.30/0.53    spl8_5 <=> r2_hidden(sK5(sK1,k1_xboole_0),sK3)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.30/0.53  fof(f158,plain,(
% 1.30/0.53    spl8_3 | spl8_5 | ~spl8_2),
% 1.30/0.53    inference(avatar_split_clause,[],[f143,f68,f155,f146])).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    spl8_2 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.30/0.53  fof(f143,plain,(
% 1.30/0.53    r2_hidden(sK5(sK1,k1_xboole_0),sK3) | k1_xboole_0 = sK1 | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f141,f37])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    r1_tarski(sK1,sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f19])).
% 1.30/0.53  fof(f141,plain,(
% 1.30/0.53    ( ! [X8,X9] : (~r1_tarski(X8,X9) | r2_hidden(sK5(X8,k1_xboole_0),X9) | k1_xboole_0 = X8) ) | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f132,f46])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f28])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(rectify,[],[f25])).
% 1.30/0.53  % (10636)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(nnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.53  fof(f132,plain,(
% 1.30/0.53    ( ! [X3] : (r2_hidden(sK5(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) ) | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f44,f69])).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_2),
% 1.30/0.53    inference(avatar_component_clause,[],[f68])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | X0 = X1 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.30/0.53    inference(nnf_transformation,[],[f14])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.30/0.53  fof(f153,plain,(
% 1.30/0.53    spl8_3 | spl8_4 | ~spl8_2),
% 1.30/0.53    inference(avatar_split_clause,[],[f142,f68,f150,f146])).
% 1.30/0.53  fof(f142,plain,(
% 1.30/0.53    r2_hidden(sK5(sK1,k1_xboole_0),sK2) | k1_xboole_0 = sK1 | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f141,f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    r1_tarski(sK1,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f19])).
% 1.30/0.53  fof(f72,plain,(
% 1.30/0.53    spl8_1),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f71])).
% 1.30/0.53  fof(f71,plain,(
% 1.30/0.53    $false | spl8_1),
% 1.30/0.53    inference(resolution,[],[f66,f38])).
% 1.30/0.53  fof(f66,plain,(
% 1.30/0.53    ~r1_xboole_0(sK2,sK3) | spl8_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f64])).
% 1.30/0.53  fof(f64,plain,(
% 1.30/0.53    spl8_1 <=> r1_xboole_0(sK2,sK3)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.30/0.53  fof(f70,plain,(
% 1.30/0.53    ~spl8_1 | spl8_2),
% 1.30/0.53    inference(avatar_split_clause,[],[f62,f68,f64])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(sK2,sK3)) )),
% 1.30/0.53    inference(superposition,[],[f43,f61])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  % (10649)Refutation not found, incomplete strategy% (10649)------------------------------
% 1.30/0.53  % (10649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (10649)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (10649)Memory used [KB]: 10618
% 1.30/0.53  % (10649)Time elapsed: 0.080 s
% 1.30/0.53  % (10649)------------------------------
% 1.30/0.53  % (10649)------------------------------
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f10])).
% 1.30/0.53  fof(f10,plain,(
% 1.30/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(rectify,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (10639)------------------------------
% 1.30/0.53  % (10639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (10639)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (10639)Memory used [KB]: 6268
% 1.30/0.53  % (10639)Time elapsed: 0.116 s
% 1.30/0.53  % (10639)------------------------------
% 1.30/0.53  % (10639)------------------------------
% 1.30/0.53  % (10630)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (10625)Success in time 0.174 s
%------------------------------------------------------------------------------
