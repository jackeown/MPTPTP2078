%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:06 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 219 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  220 ( 570 expanded)
%              Number of equality atoms :   85 ( 279 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f175,f190,f215,f231])).

fof(f231,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f82,f214,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | ~ r2_hidden(X3,X2) ) ),
    inference(condensation,[],[f108])).

fof(f108,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X4)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f88,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X2))
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f61,f48])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f214,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f82,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f215,plain,
    ( spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f196,f172,f212])).

fof(f172,plain,
    ( spl5_7
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f196,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(superposition,[],[f64,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f64,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f190,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f71,f187])).

fof(f187,plain,
    ( sK0 = sK1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f186,f100])).

fof(f100,plain,(
    ! [X0] : sK4(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(global_subsumption,[],[f79,f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK4(k2_enumset1(X0,X0,X0,X0)) = X0
      | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f186,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(superposition,[],[f100,f170])).

fof(f170,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_6
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f71,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f175,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f160,f74,f172,f168])).

fof(f74,plain,
    ( spl5_2
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f160,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f37,f52,f52])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f77,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f74])).

fof(f53,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f31,f52,f52])).

fof(f31,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f72,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.15/0.54  % (1416)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (1398)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (1407)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.54  % (1406)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.55  % (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% 1.35/0.55  % (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (1406)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (1406)Memory used [KB]: 1791
% 1.35/0.55  % (1406)Time elapsed: 0.118 s
% 1.35/0.55  % (1406)------------------------------
% 1.35/0.55  % (1406)------------------------------
% 1.35/0.55  % (1415)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.55  % (1420)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.55  % (1396)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.55  % (1412)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.55  % (1415)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f232,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f72,f77,f175,f190,f215,f231])).
% 1.35/0.55  fof(f231,plain,(
% 1.35/0.55    ~spl5_8),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f225])).
% 1.35/0.55  fof(f225,plain,(
% 1.35/0.55    $false | ~spl5_8),
% 1.35/0.55    inference(unit_resulting_resolution,[],[f82,f214,f109])).
% 1.35/0.55  fof(f109,plain,(
% 1.35/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | ~r2_hidden(X3,X2)) )),
% 1.35/0.55    inference(condensation,[],[f108])).
% 1.35/0.55  fof(f108,plain,(
% 1.35/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X4) | ~r1_xboole_0(X2,X2)) )),
% 1.35/0.55    inference(superposition,[],[f88,f48])).
% 1.35/0.55  fof(f48,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(nnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.35/0.55  fof(f88,plain,(
% 1.35/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X2)) | ~r1_xboole_0(X2,X3)) )),
% 1.35/0.55    inference(duplicate_literal_removal,[],[f85])).
% 1.35/0.55  fof(f85,plain,(
% 1.35/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X2)) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 1.35/0.55    inference(superposition,[],[f61,f48])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f42,f47])).
% 1.35/0.55  fof(f47,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f15,plain,(
% 1.35/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(ennf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,plain,(
% 1.35/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(rectify,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.35/0.55  fof(f214,plain,(
% 1.35/0.55    r2_hidden(sK0,k1_xboole_0) | ~spl5_8),
% 1.35/0.55    inference(avatar_component_clause,[],[f212])).
% 1.35/0.55  fof(f212,plain,(
% 1.35/0.55    spl5_8 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.35/0.55  fof(f82,plain,(
% 1.35/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(trivial_inequality_removal,[],[f80])).
% 1.35/0.55  fof(f80,plain,(
% 1.35/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(superposition,[],[f49,f45])).
% 1.35/0.55  fof(f45,plain,(
% 1.35/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f30])).
% 1.35/0.55  fof(f215,plain,(
% 1.35/0.55    spl5_8 | ~spl5_7),
% 1.35/0.55    inference(avatar_split_clause,[],[f196,f172,f212])).
% 1.35/0.55  fof(f172,plain,(
% 1.35/0.55    spl5_7 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.35/0.55  fof(f196,plain,(
% 1.35/0.55    r2_hidden(sK0,k1_xboole_0) | ~spl5_7),
% 1.35/0.55    inference(superposition,[],[f64,f174])).
% 1.35/0.55  fof(f174,plain,(
% 1.35/0.55    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_7),
% 1.35/0.55    inference(avatar_component_clause,[],[f172])).
% 1.35/0.55  fof(f64,plain,(
% 1.35/0.55    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.35/0.55    inference(equality_resolution,[],[f63])).
% 1.35/0.55  fof(f63,plain,(
% 1.35/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.35/0.55    inference(equality_resolution,[],[f56])).
% 1.35/0.55  fof(f56,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.35/0.55    inference(definition_unfolding,[],[f34,f52])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f40,f51])).
% 1.35/0.55  fof(f51,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f46,f50])).
% 1.35/0.55  fof(f50,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.55  fof(f46,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.55  fof(f40,plain,(
% 1.35/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.55    inference(rectify,[],[f18])).
% 1.35/0.55  fof(f18,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.35/0.55  fof(f190,plain,(
% 1.35/0.55    spl5_1 | ~spl5_6),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f188])).
% 1.35/0.55  fof(f188,plain,(
% 1.35/0.55    $false | (spl5_1 | ~spl5_6)),
% 1.35/0.55    inference(subsumption_resolution,[],[f71,f187])).
% 1.35/0.55  fof(f187,plain,(
% 1.35/0.55    sK0 = sK1 | ~spl5_6),
% 1.35/0.55    inference(forward_demodulation,[],[f186,f100])).
% 1.35/0.55  fof(f100,plain,(
% 1.35/0.55    ( ! [X0] : (sK4(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.35/0.55    inference(global_subsumption,[],[f79,f98])).
% 1.35/0.55  fof(f98,plain,(
% 1.35/0.55    ( ! [X0] : (sK4(k2_enumset1(X0,X0,X0,X0)) = X0 | v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.35/0.55    inference(resolution,[],[f65,f44])).
% 1.35/0.55  fof(f44,plain,(
% 1.35/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.35/0.55    inference(rectify,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.35/0.55  fof(f65,plain,(
% 1.35/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.35/0.55    inference(equality_resolution,[],[f57])).
% 1.35/0.55  fof(f57,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.35/0.55    inference(definition_unfolding,[],[f33,f52])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f79,plain,(
% 1.35/0.55    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.35/0.55    inference(resolution,[],[f64,f43])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f29])).
% 1.35/0.55  fof(f186,plain,(
% 1.35/0.55    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 1.35/0.55    inference(superposition,[],[f100,f170])).
% 1.35/0.55  fof(f170,plain,(
% 1.35/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_6),
% 1.35/0.55    inference(avatar_component_clause,[],[f168])).
% 1.35/0.55  fof(f168,plain,(
% 1.35/0.55    spl5_6 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.35/0.55  fof(f71,plain,(
% 1.35/0.55    sK0 != sK1 | spl5_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f69])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    spl5_1 <=> sK0 = sK1),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.35/0.55  fof(f175,plain,(
% 1.35/0.55    spl5_6 | spl5_7 | ~spl5_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f160,f74,f172,f168])).
% 1.35/0.55  fof(f74,plain,(
% 1.35/0.55    spl5_2 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.35/0.55  fof(f160,plain,(
% 1.35/0.55    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_2),
% 1.35/0.55    inference(resolution,[],[f60,f76])).
% 1.35/0.55  fof(f76,plain,(
% 1.35/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f74])).
% 1.35/0.55  fof(f60,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.35/0.55    inference(definition_unfolding,[],[f37,f52,f52])).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.35/0.55    inference(flattening,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.35/0.55    inference(nnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.35/0.55  fof(f77,plain,(
% 1.35/0.55    spl5_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f53,f74])).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.35/0.55    inference(definition_unfolding,[],[f31,f52,f52])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.35/0.55    inference(cnf_transformation,[],[f17])).
% 1.35/0.55  fof(f17,plain,(
% 1.35/0.55    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 1.35/0.55  fof(f16,plain,(
% 1.35/0.55    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f14,plain,(
% 1.35/0.55    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.35/0.55    inference(ennf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.35/0.55    inference(negated_conjecture,[],[f11])).
% 1.35/0.55  fof(f11,conjecture,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    ~spl5_1),
% 1.35/0.55    inference(avatar_split_clause,[],[f32,f69])).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    sK0 != sK1),
% 1.35/0.55    inference(cnf_transformation,[],[f17])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (1415)------------------------------
% 1.35/0.55  % (1415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (1415)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (1415)Memory used [KB]: 10874
% 1.35/0.55  % (1415)Time elapsed: 0.128 s
% 1.35/0.55  % (1415)------------------------------
% 1.35/0.55  % (1415)------------------------------
% 1.35/0.55  % (1399)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.56  % (1414)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.56  % (1391)Success in time 0.191 s
%------------------------------------------------------------------------------
