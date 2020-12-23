%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 127 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  298 ( 428 expanded)
%              Number of equality atoms :  125 ( 219 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f86,f94,f105,f119,f130,f143,f322,f323])).

fof(f323,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k2_xboole_0(k1_tarski(sK0),sK2)
    | k1_tarski(sK0) != k2_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f322,plain,
    ( spl6_18
    | spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f310,f83,f65,f319])).

fof(f319,plain,
    ( spl6_18
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f65,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f83,plain,
    ( spl6_5
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f310,plain,
    ( sK1 = k1_tarski(sK0)
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f309,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f309,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(superposition,[],[f108,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f108,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k1_tarski(X3))
      | k1_tarski(X3) = X2
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f143,plain,
    ( spl6_10
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f135,f127,f140])).

fof(f140,plain,
    ( spl6_10
  <=> sK2 = k2_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f127,plain,
    ( spl6_9
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f135,plain,
    ( sK2 = k2_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f129,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f129,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl6_9
    | spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f125,f116,f70,f127])).

fof(f70,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f116,plain,
    ( spl6_8
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f125,plain,
    ( r2_hidden(sK0,sK2)
    | spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f124,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(superposition,[],[f33,f118])).

fof(f118,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f119,plain,
    ( spl6_8
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f110,f103,f70,f116])).

fof(f103,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f110,plain,
    ( sK0 = sK3(sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f109,f72])).

fof(f109,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_7 ),
    inference(resolution,[],[f104,f33])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f96,f92,f103])).

fof(f92,plain,
    ( spl6_6
  <=> ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_6 ),
    inference(resolution,[],[f93,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f93,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f90,f75,f92])).

fof(f75,plain,
    ( spl6_4
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f90,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_4 ),
    inference(superposition,[],[f56,f77])).

fof(f77,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f86,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f79,f75,f83])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl6_4 ),
    inference(superposition,[],[f34,f77])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f78,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f73,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f60,plain,
    ( spl6_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (17120)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.44  % (17120)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.45  % (17134)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.45  % (17136)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f324,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f86,f94,f105,f119,f130,f143,f322,f323])).
% 0.20/0.45  fof(f323,plain,(
% 0.20/0.45    sK1 != k1_tarski(sK0) | sK2 != k2_xboole_0(k1_tarski(sK0),sK2) | k1_tarski(sK0) != k2_xboole_0(sK1,sK2) | sK1 = sK2),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f322,plain,(
% 0.20/0.45    spl6_18 | spl6_2 | ~spl6_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f310,f83,f65,f319])).
% 0.20/0.45  fof(f319,plain,(
% 0.20/0.45    spl6_18 <=> sK1 = k1_tarski(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    spl6_2 <=> k1_xboole_0 = sK1),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    spl6_5 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.45  fof(f310,plain,(
% 0.20/0.45    sK1 = k1_tarski(sK0) | (spl6_2 | ~spl6_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f309,f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    k1_xboole_0 != sK1 | spl6_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f65])).
% 0.20/0.45  fof(f309,plain,(
% 0.20/0.45    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl6_5),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f308])).
% 0.20/0.45  fof(f308,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl6_5),
% 0.20/0.45    inference(superposition,[],[f108,f85])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl6_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f83])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k1_tarski(X3)) | k1_tarski(X3) = X2 | k1_xboole_0 = X2) )),
% 0.20/0.45    inference(resolution,[],[f40,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.45    inference(flattening,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    spl6_10 | ~spl6_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f135,f127,f140])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    spl6_10 <=> sK2 = k2_xboole_0(k1_tarski(sK0),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    spl6_9 <=> r2_hidden(sK0,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    sK2 = k2_xboole_0(k1_tarski(sK0),sK2) | ~spl6_9),
% 0.20/0.45    inference(resolution,[],[f129,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.45  fof(f129,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2) | ~spl6_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f127])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    spl6_9 | spl6_3 | ~spl6_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f125,f116,f70,f127])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    spl6_3 <=> k1_xboole_0 = sK2),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    spl6_8 <=> sK0 = sK3(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2) | (spl6_3 | ~spl6_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f124,f72])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    k1_xboole_0 != sK2 | spl6_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f70])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl6_8),
% 0.20/0.45    inference(superposition,[],[f33,f118])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    sK0 = sK3(sK2) | ~spl6_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f116])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    spl6_8 | spl6_3 | ~spl6_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f110,f103,f70,f116])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl6_7 <=> ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    sK0 = sK3(sK2) | (spl6_3 | ~spl6_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f109,f72])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl6_7),
% 0.20/0.45    inference(resolution,[],[f104,f33])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl6_7 | ~spl6_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f96,f92,f103])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    spl6_6 <=> ! [X0] : (r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_6),
% 0.20/0.45    inference(resolution,[],[f93,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.45    inference(equality_resolution,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.45    inference(rectify,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl6_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f92])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl6_6 | ~spl6_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f90,f75,f92])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    spl6_4 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl6_4),
% 0.20/0.45    inference(superposition,[],[f56,f77])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl6_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f75])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.45    inference(equality_resolution,[],[f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.45    inference(rectify,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.45    inference(flattening,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl6_5 | ~spl6_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f79,f75,f83])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl6_4),
% 0.20/0.45    inference(superposition,[],[f34,f77])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f29,f75])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ~spl6_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f70])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    k1_xboole_0 != sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ~spl6_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f31,f65])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    k1_xboole_0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~spl6_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl6_1 <=> sK1 = sK2),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    sK1 != sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (17120)------------------------------
% 0.20/0.46  % (17120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (17120)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (17120)Memory used [KB]: 6268
% 0.20/0.46  % (17120)Time elapsed: 0.067 s
% 0.20/0.46  % (17120)------------------------------
% 0.20/0.46  % (17120)------------------------------
% 0.20/0.46  % (17117)Success in time 0.103 s
%------------------------------------------------------------------------------
