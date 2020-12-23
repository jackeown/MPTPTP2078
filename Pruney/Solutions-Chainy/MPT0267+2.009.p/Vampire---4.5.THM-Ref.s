%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 129 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  312 ( 749 expanded)
%              Number of equality atoms :  121 ( 264 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f72,f97,f131,f137,f157])).

fof(f157,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f50,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f143,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f136,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f137,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f132,f62,f58,f134])).

% (13971)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (13969)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f58,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f62,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f132,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f59,f64])).

fof(f64,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f59,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f131,plain,
    ( spl5_4
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f130,f69,f58,f92])).

fof(f92,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f130,plain,
    ( r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f114,f71])).

fof(f71,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f114,plain,
    ( r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f97,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f82,f62,f92])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f63,f63,f63,f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f67,f69])).

fof(f67,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f23,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK0 = sK2
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
    & ( ( sK0 != sK2
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK0 = sK2
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
      & ( ( sK0 != sK2
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f66,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f43,f62,f58])).

fof(f43,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f56,f62,f58])).

fof(f56,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(subsumption_resolution,[],[f42,f48])).

fof(f42,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:26:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (13994)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (13985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (13988)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (13994)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f65,f66,f72,f97,f131,f137,f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ~spl5_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    $false | ~spl5_7),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.22/0.52    inference(equality_resolution,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.22/0.52    inference(equality_resolution,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(nnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~spl5_7),
% 0.22/0.52    inference(resolution,[],[f136,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl5_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    spl5_7 <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    spl5_7 | ~spl5_1 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f62,f58,f134])).
% 0.22/0.52  % (13971)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (13969)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl5_1 <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl5_2 <=> sK0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | (~spl5_1 | ~spl5_2)),
% 0.22/0.52    inference(forward_demodulation,[],[f59,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    sK0 = sK2 | ~spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) | ~spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl5_4 | spl5_1 | ~spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f130,f69,f58,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl5_4 <=> r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl5_3 <=> r2_hidden(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2)) | (spl5_1 | ~spl5_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2)) | ~r2_hidden(sK0,sK1) | spl5_1),
% 0.22/0.52    inference(resolution,[],[f60,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2))) | spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ~spl5_4 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f82,f62,f92])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2)) | spl5_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f63,f63,f63,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    sK0 != sK2 | spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f67,f69])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f44,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.52    inference(definition_unfolding,[],[f23,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    (sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.52    inference(nnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl5_1 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f62,f58])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f26])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ~spl5_1 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f56,f62,f58])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f48])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f26])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13994)------------------------------
% 0.22/0.52  % (13994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13994)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13994)Memory used [KB]: 6268
% 0.22/0.52  % (13994)Time elapsed: 0.071 s
% 0.22/0.52  % (13994)------------------------------
% 0.22/0.52  % (13994)------------------------------
% 0.22/0.52  % (13976)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (13960)Success in time 0.16 s
%------------------------------------------------------------------------------
