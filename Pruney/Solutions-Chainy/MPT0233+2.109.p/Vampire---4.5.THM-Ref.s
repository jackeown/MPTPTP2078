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
% DateTime   : Thu Dec  3 12:37:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 708 expanded)
%              Number of leaves         :   25 ( 228 expanded)
%              Depth                    :   16
%              Number of atoms          :  331 (1400 expanded)
%              Number of equality atoms :  192 (1015 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f336,f376,f417,f452,f465,f472])).

fof(f472,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f470,f42])).

fof(f42,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f470,plain,
    ( sK1 = sK4
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f468,f41])).

fof(f41,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f468,plain,
    ( sK1 = sK3
    | sK1 = sK4
    | ~ spl6_1 ),
    inference(resolution,[],[f136,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f54,f98])).

fof(f98,plain,(
    ! [X0,X1] : sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f7,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

% (24794)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f136,plain,
    ( r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_1
  <=> r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f465,plain,
    ( spl6_3
    | spl6_6
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f464,f270,f266,f274,f262])).

fof(f262,plain,
    ( spl6_3
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f274,plain,
    ( spl6_6
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f266,plain,
    ( spl6_4
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f270,plain,
    ( spl6_5
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f464,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f463,f267])).

fof(f267,plain,
    ( k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f266])).

fof(f463,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f461,f271])).

fof(f271,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f270])).

fof(f461,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(resolution,[],[f81,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f62,f79,f80,f80,f79])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f79])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f81,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f40,f79,f79])).

fof(f40,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f452,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f421,f113])).

fof(f113,plain,(
    ! [X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f98,f97])).

fof(f97,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f421,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f240,f276])).

fof(f276,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f274])).

fof(f240,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(extensionality_resolution,[],[f231,f42])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
      | X2 = X3 ) ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,(
    ! [X2,X3] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
      | X2 = X3 ) ),
    inference(superposition,[],[f94,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f80,f48,f80,f80])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f67,f80,f48,f79])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f417,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f386,f113])).

fof(f386,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f238,f272])).

fof(f272,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f270])).

fof(f238,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(extensionality_resolution,[],[f231,f41])).

fof(f376,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f374,f144])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(forward_demodulation,[],[f143,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f143,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(subsumption_resolution,[],[f130,f113])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(superposition,[],[f94,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f374,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f364,f109])).

fof(f109,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f102,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f364,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl6_4 ),
    inference(superposition,[],[f183,f268])).

fof(f268,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f266])).

fof(f183,plain,(
    ! [X4,X3] : k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(superposition,[],[f124,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f124,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(resolution,[],[f100,f49])).

fof(f100,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f65,f79,f80])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f336,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f312,f113])).

fof(f312,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl6_1
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f137,f264])).

fof(f264,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f262])).

fof(f137,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24792)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (24783)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (24775)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24771)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (24773)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (24772)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (24770)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (24770)Refutation not found, incomplete strategy% (24770)------------------------------
% 0.21/0.52  % (24770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24770)Memory used [KB]: 1663
% 0.21/0.52  % (24770)Time elapsed: 0.097 s
% 0.21/0.52  % (24770)------------------------------
% 0.21/0.52  % (24770)------------------------------
% 0.21/0.52  % (24769)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (24780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (24790)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (24786)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (24787)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (24781)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (24777)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (24781)Refutation not found, incomplete strategy% (24781)------------------------------
% 0.21/0.54  % (24781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24781)Memory used [KB]: 10618
% 0.21/0.54  % (24781)Time elapsed: 0.123 s
% 0.21/0.54  % (24781)------------------------------
% 0.21/0.54  % (24781)------------------------------
% 0.21/0.54  % (24778)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (24795)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24797)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24793)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (24789)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (24796)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (24785)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (24798)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (24798)Refutation not found, incomplete strategy% (24798)------------------------------
% 0.21/0.55  % (24798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24798)Memory used [KB]: 1663
% 0.21/0.55  % (24798)Time elapsed: 0.001 s
% 0.21/0.55  % (24798)------------------------------
% 0.21/0.55  % (24798)------------------------------
% 0.21/0.55  % (24788)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (24776)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (24784)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (24774)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (24779)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (24785)Refutation not found, incomplete strategy% (24785)------------------------------
% 0.21/0.56  % (24785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24785)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24785)Memory used [KB]: 10618
% 0.21/0.56  % (24785)Time elapsed: 0.139 s
% 0.21/0.56  % (24785)------------------------------
% 0.21/0.56  % (24785)------------------------------
% 0.21/0.56  % (24775)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f473,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f336,f376,f417,f452,f465,f472])).
% 1.44/0.56  fof(f472,plain,(
% 1.44/0.56    ~spl6_1),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f471])).
% 1.44/0.56  fof(f471,plain,(
% 1.44/0.56    $false | ~spl6_1),
% 1.44/0.56    inference(subsumption_resolution,[],[f470,f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    sK1 != sK4),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.56    inference(ennf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.56    inference(negated_conjecture,[],[f18])).
% 1.44/0.56  fof(f18,conjecture,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.44/0.56  fof(f470,plain,(
% 1.44/0.56    sK1 = sK4 | ~spl6_1),
% 1.44/0.56    inference(subsumption_resolution,[],[f468,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    sK1 != sK3),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f468,plain,(
% 1.44/0.56    sK1 = sK3 | sK1 = sK4 | ~spl6_1),
% 1.44/0.56    inference(resolution,[],[f136,f115])).
% 1.44/0.56  fof(f115,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.44/0.56    inference(resolution,[],[f54,f98])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ( ! [X0,X1] : (sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.56    inference(equality_resolution,[],[f85])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.44/0.56    inference(definition_unfolding,[],[f60,f79])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f47,f78])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f52,f77])).
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f71,f76])).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f72,f75])).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f73,f74])).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.44/0.56  fof(f71,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.44/0.56    inference(cnf_transformation,[],[f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.44/0.56    inference(nnf_transformation,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.44/0.56    inference(definition_folding,[],[f7,f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.44/0.56    inference(cnf_transformation,[],[f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.44/0.56    inference(rectify,[],[f31])).
% 1.44/0.56  % (24794)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.44/0.56    inference(flattening,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.44/0.56    inference(nnf_transformation,[],[f25])).
% 1.44/0.56  fof(f136,plain,(
% 1.44/0.56    r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~spl6_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f135])).
% 1.44/0.56  fof(f135,plain,(
% 1.44/0.56    spl6_1 <=> r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.44/0.56  fof(f465,plain,(
% 1.44/0.56    spl6_3 | spl6_6 | spl6_4 | spl6_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f464,f270,f266,f274,f262])).
% 1.44/0.56  fof(f262,plain,(
% 1.44/0.56    spl6_3 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.44/0.56  fof(f274,plain,(
% 1.44/0.56    spl6_6 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.44/0.56  fof(f266,plain,(
% 1.44/0.56    spl6_4 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.44/0.56  fof(f270,plain,(
% 1.44/0.56    spl6_5 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.44/0.56  fof(f464,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | (spl6_4 | spl6_5)),
% 1.44/0.56    inference(subsumption_resolution,[],[f463,f267])).
% 1.44/0.56  fof(f267,plain,(
% 1.44/0.56    k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | spl6_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f266])).
% 1.44/0.56  fof(f463,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | spl6_5),
% 1.44/0.56    inference(subsumption_resolution,[],[f461,f271])).
% 1.44/0.56  fof(f271,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | spl6_5),
% 1.44/0.56    inference(avatar_component_clause,[],[f270])).
% 1.44/0.56  fof(f461,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 1.44/0.56    inference(resolution,[],[f81,f90])).
% 1.44/0.56  fof(f90,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 1.44/0.56    inference(definition_unfolding,[],[f62,f79,f80,f80,f79])).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f44,f79])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.44/0.56    inference(flattening,[],[f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.44/0.56    inference(nnf_transformation,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.44/0.56    inference(definition_unfolding,[],[f40,f79,f79])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f452,plain,(
% 1.44/0.56    ~spl6_6),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f451])).
% 1.44/0.56  fof(f451,plain,(
% 1.44/0.56    $false | ~spl6_6),
% 1.44/0.56    inference(subsumption_resolution,[],[f421,f113])).
% 1.44/0.56  fof(f113,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.56    inference(resolution,[],[f98,f97])).
% 1.44/0.56  fof(f97,plain,(
% 1.44/0.56    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.44/0.56    inference(equality_resolution,[],[f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f34])).
% 1.44/0.56  fof(f421,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl6_6),
% 1.44/0.56    inference(backward_demodulation,[],[f240,f276])).
% 1.44/0.56  fof(f276,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl6_6),
% 1.44/0.56    inference(avatar_component_clause,[],[f274])).
% 1.44/0.56  fof(f240,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.44/0.56    inference(extensionality_resolution,[],[f231,f42])).
% 1.44/0.56  fof(f231,plain,(
% 1.44/0.56    ( ! [X2,X3] : (~r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) | X2 = X3) )),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f230])).
% 1.44/0.56  fof(f230,plain,(
% 1.44/0.56    ( ! [X2,X3] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) | ~r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) | X2 = X3) )),
% 1.44/0.56    inference(superposition,[],[f94,f82])).
% 1.44/0.56  fof(f82,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | X0 = X1) )),
% 1.44/0.56    inference(definition_unfolding,[],[f51,f80,f48,f80,f80])).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.44/0.56    inference(nnf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,axiom,(
% 1.44/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.44/0.56  fof(f94,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) | ~r2_hidden(X0,X2)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f67,f80,f48,f79])).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.44/0.56    inference(flattening,[],[f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.44/0.56    inference(nnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.44/0.56  fof(f417,plain,(
% 1.44/0.56    ~spl6_5),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f416])).
% 1.44/0.56  fof(f416,plain,(
% 1.44/0.56    $false | ~spl6_5),
% 1.44/0.56    inference(subsumption_resolution,[],[f386,f113])).
% 1.44/0.56  fof(f386,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl6_5),
% 1.44/0.56    inference(backward_demodulation,[],[f238,f272])).
% 1.44/0.56  fof(f272,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl6_5),
% 1.44/0.56    inference(avatar_component_clause,[],[f270])).
% 1.44/0.56  fof(f238,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.44/0.56    inference(extensionality_resolution,[],[f231,f41])).
% 1.44/0.56  fof(f376,plain,(
% 1.44/0.56    ~spl6_4),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f375])).
% 1.44/0.56  fof(f375,plain,(
% 1.44/0.56    $false | ~spl6_4),
% 1.44/0.56    inference(subsumption_resolution,[],[f374,f144])).
% 1.44/0.56  fof(f144,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f143,f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.44/0.56  fof(f143,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f130,f113])).
% 1.44/0.56  fof(f130,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.56    inference(superposition,[],[f94,f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.56    inference(rectify,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.44/0.56  fof(f374,plain,(
% 1.44/0.56    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_4),
% 1.44/0.56    inference(forward_demodulation,[],[f364,f109])).
% 1.44/0.56  fof(f109,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.56    inference(resolution,[],[f102,f49])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.56  fof(f102,plain,(
% 1.44/0.56    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.44/0.56    inference(equality_resolution,[],[f89])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 1.44/0.56    inference(definition_unfolding,[],[f63,f79])).
% 1.44/0.56  fof(f63,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f364,plain,(
% 1.44/0.56    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl6_4),
% 1.44/0.56    inference(superposition,[],[f183,f268])).
% 1.44/0.56  fof(f268,plain,(
% 1.44/0.56    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl6_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f266])).
% 1.44/0.56  fof(f183,plain,(
% 1.44/0.56    ( ! [X4,X3] : (k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.44/0.56    inference(superposition,[],[f124,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.56  fof(f124,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 1.44/0.56    inference(resolution,[],[f100,f49])).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.44/0.56    inference(equality_resolution,[],[f87])).
% 1.44/0.56  fof(f87,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 1.44/0.56    inference(definition_unfolding,[],[f65,f79,f80])).
% 1.44/0.56  fof(f65,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f336,plain,(
% 1.44/0.56    spl6_1 | ~spl6_3),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f335])).
% 1.44/0.56  fof(f335,plain,(
% 1.44/0.56    $false | (spl6_1 | ~spl6_3)),
% 1.44/0.56    inference(subsumption_resolution,[],[f312,f113])).
% 1.44/0.56  fof(f312,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (spl6_1 | ~spl6_3)),
% 1.44/0.56    inference(backward_demodulation,[],[f137,f264])).
% 1.44/0.56  fof(f264,plain,(
% 1.44/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | ~spl6_3),
% 1.44/0.56    inference(avatar_component_clause,[],[f262])).
% 1.44/0.56  fof(f137,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl6_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f135])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (24775)------------------------------
% 1.44/0.56  % (24775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (24775)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (24775)Memory used [KB]: 11001
% 1.44/0.56  % (24775)Time elapsed: 0.091 s
% 1.44/0.56  % (24775)------------------------------
% 1.44/0.56  % (24775)------------------------------
% 1.44/0.57  % (24768)Success in time 0.199 s
%------------------------------------------------------------------------------
