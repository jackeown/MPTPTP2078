%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 172 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  331 ( 805 expanded)
%              Number of equality atoms :  120 ( 173 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f973,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f107,f883,f972])).

fof(f972,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f956,f105])).

fof(f105,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_2
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f956,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f892,f153])).

fof(f153,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6)) ),
    inference(resolution,[],[f97,f94])).

% (31293)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f94,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP1(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f97,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f21,f24])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f892,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f138,f100])).

fof(f100,plain,
    ( sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_1
  <=> sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f62,f93])).

fof(f93,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f883,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f882])).

fof(f882,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f852,f101])).

fof(f101,plain,
    ( sK2 != k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f852,plain,
    ( sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | spl6_2 ),
    inference(superposition,[],[f596,f666])).

fof(f666,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2)
    | spl6_2 ),
    inference(resolution,[],[f230,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f230,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

% (31275)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f596,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(resolution,[],[f591,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f591,plain,(
    ! [X4,X5] : sP0(k4_xboole_0(X4,X5),X5,X5) ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,(
    ! [X4,X5] :
      ( sP0(k4_xboole_0(X4,X5),X5,X5)
      | sP0(k4_xboole_0(X4,X5),X5,X5) ) ),
    inference(resolution,[],[f391,f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f391,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X3,X4),X5,X5),X4)
      | sP0(k4_xboole_0(X3,X4),X5,X5) ) ),
    inference(resolution,[],[f345,f138])).

fof(f345,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(X1,X2,X2),X1)
      | sP0(X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f343,f64])).

fof(f343,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK4(X1,X2,X2),X1)
      | ~ r2_hidden(sK4(X1,X2,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK4(X1,X2,X2),X1)
      | ~ r2_hidden(sK4(X1,X2,X2),X2)
      | sP0(X1,X2,X2) ) ),
    inference(resolution,[],[f263,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f85,f103,f99])).

fof(f85,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f44,f82])).

fof(f44,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r2_hidden(sK3,sK2)
      | sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) )
    & ( ~ r2_hidden(sK3,sK2)
      | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) )
      & ( ~ r2_hidden(sK3,sK2)
        | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f106,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f84,f103,f99])).

fof(f84,plain,
    ( r2_hidden(sK3,sK2)
    | sK2 != k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f45,plain,
    ( r2_hidden(sK3,sK2)
    | sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:11:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (31268)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (31277)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (31277)Refutation not found, incomplete strategy% (31277)------------------------------
% 0.22/0.51  % (31277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31278)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (31273)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31277)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31277)Memory used [KB]: 10746
% 0.22/0.52  % (31277)Time elapsed: 0.096 s
% 0.22/0.52  % (31277)------------------------------
% 0.22/0.52  % (31277)------------------------------
% 0.22/0.52  % (31267)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (31286)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (31267)Refutation not found, incomplete strategy% (31267)------------------------------
% 0.22/0.52  % (31267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31267)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31267)Memory used [KB]: 1663
% 0.22/0.52  % (31267)Time elapsed: 0.101 s
% 0.22/0.52  % (31267)------------------------------
% 0.22/0.52  % (31267)------------------------------
% 0.22/0.53  % (31284)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (31284)Refutation not found, incomplete strategy% (31284)------------------------------
% 0.22/0.53  % (31284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31284)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31284)Memory used [KB]: 1663
% 0.22/0.53  % (31284)Time elapsed: 0.121 s
% 0.22/0.53  % (31284)------------------------------
% 0.22/0.53  % (31284)------------------------------
% 0.22/0.53  % (31282)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (31266)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (31290)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (31279)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (31278)Refutation not found, incomplete strategy% (31278)------------------------------
% 0.22/0.54  % (31278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31278)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31278)Memory used [KB]: 6140
% 0.22/0.54  % (31278)Time elapsed: 0.122 s
% 0.22/0.54  % (31278)------------------------------
% 0.22/0.54  % (31278)------------------------------
% 0.22/0.54  % (31271)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (31269)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (31270)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (31276)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (31296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (31291)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (31274)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (31295)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (31288)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (31289)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (31297)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (31280)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (31281)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (31283)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (31285)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (31281)Refutation not found, incomplete strategy% (31281)------------------------------
% 0.22/0.55  % (31281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31297)Refutation not found, incomplete strategy% (31297)------------------------------
% 0.22/0.55  % (31297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31281)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31281)Memory used [KB]: 1663
% 0.22/0.55  % (31281)Time elapsed: 0.140 s
% 0.22/0.55  % (31281)------------------------------
% 0.22/0.55  % (31281)------------------------------
% 0.22/0.55  % (31283)Refutation not found, incomplete strategy% (31283)------------------------------
% 0.22/0.55  % (31283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31283)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31283)Memory used [KB]: 10618
% 0.22/0.55  % (31283)Time elapsed: 0.136 s
% 0.22/0.55  % (31283)------------------------------
% 0.22/0.55  % (31283)------------------------------
% 0.22/0.55  % (31297)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31297)Memory used [KB]: 1663
% 0.22/0.55  % (31297)Time elapsed: 0.004 s
% 0.22/0.55  % (31297)------------------------------
% 0.22/0.55  % (31297)------------------------------
% 0.22/0.55  % (31287)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (31292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (31273)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f973,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f106,f107,f883,f972])).
% 0.22/0.57  fof(f972,plain,(
% 0.22/0.57    ~spl6_1 | ~spl6_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f971])).
% 0.22/0.57  fof(f971,plain,(
% 0.22/0.57    $false | (~spl6_1 | ~spl6_2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f956,f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    r2_hidden(sK3,sK2) | ~spl6_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f103])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    spl6_2 <=> r2_hidden(sK3,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.57  fof(f956,plain,(
% 0.22/0.57    ~r2_hidden(sK3,sK2) | ~spl6_1),
% 0.22/0.57    inference(resolution,[],[f892,f153])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6))) )),
% 0.22/0.57    inference(resolution,[],[f97,f94])).
% 0.22/0.57  % (31293)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    ( ! [X2,X5,X3,X1] : (~sP1(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 0.22/0.57    inference(equality_resolution,[],[f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.57    inference(rectify,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.22/0.57    inference(flattening,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.22/0.57    inference(nnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 0.22/0.57    inference(equality_resolution,[],[f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.57    inference(definition_unfolding,[],[f78,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f60,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.57    inference(nnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.22/0.57    inference(definition_folding,[],[f21,f24])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.58/0.57  fof(f892,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X1,sK2)) ) | ~spl6_1),
% 1.58/0.57    inference(superposition,[],[f138,f100])).
% 1.58/0.57  fof(f100,plain,(
% 1.58/0.57    sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~spl6_1),
% 1.58/0.57    inference(avatar_component_clause,[],[f99])).
% 1.58/0.57  fof(f99,plain,(
% 1.58/0.57    spl6_1 <=> sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.58/0.57  fof(f138,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.58/0.57    inference(resolution,[],[f62,f93])).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.57    inference(equality_resolution,[],[f67])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.58/0.57    inference(cnf_transformation,[],[f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.58/0.57    inference(nnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.58/0.57    inference(definition_folding,[],[f2,f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.58/0.57  fof(f62,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f36])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.57    inference(rectify,[],[f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.58/0.57    inference(flattening,[],[f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.58/0.57    inference(nnf_transformation,[],[f22])).
% 1.58/0.57  fof(f883,plain,(
% 1.58/0.57    spl6_1 | spl6_2),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f882])).
% 1.58/0.57  fof(f882,plain,(
% 1.58/0.57    $false | (spl6_1 | spl6_2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f852,f101])).
% 1.58/0.57  fof(f101,plain,(
% 1.58/0.57    sK2 != k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | spl6_1),
% 1.58/0.57    inference(avatar_component_clause,[],[f99])).
% 1.58/0.57  fof(f852,plain,(
% 1.58/0.57    sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | spl6_2),
% 1.58/0.57    inference(superposition,[],[f596,f666])).
% 1.58/0.57  fof(f666,plain,(
% 1.58/0.57    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) | spl6_2),
% 1.58/0.57    inference(resolution,[],[f230,f104])).
% 1.58/0.57  fof(f104,plain,(
% 1.58/0.57    ~r2_hidden(sK3,sK2) | spl6_2),
% 1.58/0.57    inference(avatar_component_clause,[],[f103])).
% 1.58/0.57  fof(f230,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.58/0.57    inference(resolution,[],[f87,f58])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.58/0.57    inference(nnf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.58/0.57  fof(f87,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f53,f82])).
% 1.58/0.57  fof(f82,plain,(
% 1.58/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f48,f81])).
% 1.58/0.57  fof(f81,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f50,f80])).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f12])).
% 1.58/0.57  fof(f12,axiom,(
% 1.58/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,axiom,(
% 1.58/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.58/0.57  % (31275)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.58/0.57  fof(f596,plain,(
% 1.58/0.57    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 1.58/0.57    inference(resolution,[],[f591,f68])).
% 1.58/0.57  fof(f68,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.58/0.57    inference(cnf_transformation,[],[f37])).
% 1.58/0.57  fof(f591,plain,(
% 1.58/0.57    ( ! [X4,X5] : (sP0(k4_xboole_0(X4,X5),X5,X5)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f578])).
% 1.58/0.57  fof(f578,plain,(
% 1.58/0.57    ( ! [X4,X5] : (sP0(k4_xboole_0(X4,X5),X5,X5) | sP0(k4_xboole_0(X4,X5),X5,X5)) )),
% 1.58/0.57    inference(resolution,[],[f391,f263])).
% 1.58/0.57  fof(f263,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.58/0.57    inference(factoring,[],[f64])).
% 1.58/0.57  fof(f64,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f36])).
% 1.58/0.57  fof(f391,plain,(
% 1.58/0.57    ( ! [X4,X5,X3] : (~r2_hidden(sK4(k4_xboole_0(X3,X4),X5,X5),X4) | sP0(k4_xboole_0(X3,X4),X5,X5)) )),
% 1.58/0.57    inference(resolution,[],[f345,f138])).
% 1.58/0.57  fof(f345,plain,(
% 1.58/0.57    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X2),X1) | sP0(X1,X2,X2)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f343,f64])).
% 1.58/0.57  fof(f343,plain,(
% 1.58/0.57    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK4(X1,X2,X2),X1) | ~r2_hidden(sK4(X1,X2,X2),X2)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f338])).
% 1.58/0.57  fof(f338,plain,(
% 1.58/0.57    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK4(X1,X2,X2),X1) | ~r2_hidden(sK4(X1,X2,X2),X2) | sP0(X1,X2,X2)) )),
% 1.58/0.57    inference(resolution,[],[f263,f66])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f36])).
% 1.58/0.57  fof(f107,plain,(
% 1.58/0.57    spl6_1 | ~spl6_2),
% 1.58/0.57    inference(avatar_split_clause,[],[f85,f103,f99])).
% 1.58/0.57  fof(f85,plain,(
% 1.58/0.57    ~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 1.58/0.57    inference(definition_unfolding,[],[f44,f82])).
% 1.58/0.57  fof(f44,plain,(
% 1.58/0.57    ~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    (r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k1_tarski(sK3))) & (~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k1_tarski(sK3))) & (~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.58/0.57    inference(nnf_transformation,[],[f18])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f17])).
% 1.58/0.57  fof(f17,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.58/0.57    inference(negated_conjecture,[],[f16])).
% 1.58/0.57  fof(f16,conjecture,(
% 1.58/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.58/0.57  fof(f106,plain,(
% 1.58/0.57    ~spl6_1 | spl6_2),
% 1.58/0.57    inference(avatar_split_clause,[],[f84,f103,f99])).
% 1.58/0.57  fof(f84,plain,(
% 1.58/0.57    r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 1.58/0.57    inference(definition_unfolding,[],[f45,f82])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (31273)------------------------------
% 1.58/0.57  % (31273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (31273)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (31273)Memory used [KB]: 11257
% 1.58/0.57  % (31273)Time elapsed: 0.148 s
% 1.58/0.57  % (31273)------------------------------
% 1.58/0.57  % (31273)------------------------------
% 1.58/0.57  % (31262)Success in time 0.205 s
%------------------------------------------------------------------------------
