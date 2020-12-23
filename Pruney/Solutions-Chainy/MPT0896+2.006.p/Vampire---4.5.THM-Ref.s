%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 694 expanded)
%              Number of leaves         :   21 ( 210 expanded)
%              Depth                    :   22
%              Number of atoms          :  544 (2881 expanded)
%              Number of equality atoms :  371 (2647 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f843,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f149,f171,f190,f237,f243,f406,f485,f501,f519,f713,f799,f840,f842])).

fof(f842,plain,
    ( spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f841])).

fof(f841,plain,
    ( $false
    | spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f74,f272])).

fof(f272,plain,
    ( sK3 = sK7
    | spl8_7 ),
    inference(equality_resolution,[],[f264])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK7 = X2 )
    | spl8_7 ),
    inference(subsumption_resolution,[],[f256,f92])).

fof(f92,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_7
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK7 = X2 ) ),
    inference(superposition,[],[f51,f43])).

fof(f43,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f21,f42,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f21,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f41,f30,f30,f30])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f74,plain,
    ( sK3 != sK7
    | spl8_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f840,plain,
    ( spl8_3
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f839])).

fof(f839,plain,
    ( $false
    | spl8_3
    | spl8_7 ),
    inference(subsumption_resolution,[],[f327,f70])).

fof(f70,plain,
    ( sK2 != sK6
    | spl8_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f327,plain,
    ( sK2 = sK6
    | spl8_7 ),
    inference(equality_resolution,[],[f305])).

fof(f305,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK6 = X1 )
    | spl8_7 ),
    inference(subsumption_resolution,[],[f297,f92])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK6 = X1 )
    | spl8_7 ),
    inference(superposition,[],[f52,f276])).

fof(f276,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | spl8_7 ),
    inference(backward_demodulation,[],[f43,f272])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f40,f30,f30,f30])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f799,plain,
    ( spl8_1
    | spl8_5
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f798])).

fof(f798,plain,
    ( $false
    | spl8_1
    | spl8_5
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(trivial_inequality_removal,[],[f797])).

fof(f797,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1
    | spl8_5
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(superposition,[],[f83,f759])).

fof(f759,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | spl8_1
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f755,f62])).

fof(f62,plain,
    ( sK0 != sK4
    | spl8_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f755,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK0 = sK4 )
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(equality_resolution,[],[f692])).

fof(f692,plain,
    ( ! [X19,X17,X20,X18] :
        ( k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)
        | k1_xboole_0 = X17
        | sK4 = X18 )
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f691,f114])).

fof(f114,plain,
    ( k1_xboole_0 != sK4
    | spl8_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f691,plain,
    ( ! [X19,X17,X20,X18] :
        ( k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)
        | k1_xboole_0 = X17
        | k1_xboole_0 = sK4
        | sK4 = X18 )
    | spl8_7
    | spl8_10 ),
    inference(subsumption_resolution,[],[f677,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK5
    | spl8_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f677,plain,
    ( ! [X19,X17,X20,X18] :
        ( k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)
        | k1_xboole_0 = X17
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK4 = X18 )
    | spl8_7 ),
    inference(superposition,[],[f50,f367])).

fof(f367,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | spl8_7 ),
    inference(equality_resolution,[],[f319])).

fof(f319,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k2_zfmisc_1(sK4,sK5) = X0 )
    | spl8_7 ),
    inference(subsumption_resolution,[],[f311,f92])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k2_zfmisc_1(sK4,sK5) = X0 )
    | spl8_7 ),
    inference(superposition,[],[f53,f276])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f39,f30,f30,f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f36,f30,f30])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f11])).

% (6376)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f83,plain,
    ( k1_xboole_0 != sK7
    | spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f713,plain,
    ( spl8_2
    | spl8_13
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f709,f117,f113,f90,f131,f64])).

fof(f64,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f131,plain,
    ( spl8_13
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f709,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 = sK5 )
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(equality_resolution,[],[f690])).

fof(f690,plain,
    ( ! [X12,X10,X11,X9] :
        ( k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9)
        | k1_xboole_0 = X9
        | sK5 = X11 )
    | spl8_7
    | spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f689,f114])).

fof(f689,plain,
    ( ! [X12,X10,X11,X9] :
        ( k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9)
        | k1_xboole_0 = X9
        | k1_xboole_0 = sK4
        | sK5 = X11 )
    | spl8_7
    | spl8_10 ),
    inference(subsumption_resolution,[],[f675,f118])).

fof(f675,plain,
    ( ! [X12,X10,X11,X9] :
        ( k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9)
        | k1_xboole_0 = X9
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X11 )
    | spl8_7 ),
    inference(superposition,[],[f49,f367])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f37,f30,f30])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f519,plain,(
    ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f517,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f517,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f516,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f516,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f515])).

fof(f515,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(superposition,[],[f27,f513])).

fof(f513,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f511,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f511,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f510])).

fof(f510,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_14 ),
    inference(superposition,[],[f27,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_14
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f501,plain,
    ( spl8_6
    | ~ spl8_7
    | spl8_5 ),
    inference(avatar_split_clause,[],[f500,f82,f90,f86])).

fof(f86,plain,
    ( spl8_6
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f500,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f499,f83])).

fof(f499,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = sK7 ),
    inference(superposition,[],[f27,f43])).

fof(f485,plain,(
    ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f483,f23])).

fof(f483,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f481,f22])).

fof(f481,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(trivial_inequality_removal,[],[f480])).

fof(f480,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(superposition,[],[f27,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f204,f24])).

fof(f204,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f203,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10 ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10 ),
    inference(superposition,[],[f47,f196])).

fof(f196,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f195,f55])).

fof(f55,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f195,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f194,f55])).

% (6392)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f194,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f193,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f193,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f43,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f406,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_split_clause,[],[f405,f121,f86,f131,f127])).

fof(f127,plain,
    ( spl8_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f121,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f405,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) )
    | ~ spl8_6
    | spl8_11 ),
    inference(subsumption_resolution,[],[f125,f122])).

fof(f122,plain,
    ( k1_xboole_0 != sK6
    | spl8_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) )
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f108,f55])).

fof(f108,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) )
    | ~ spl8_6 ),
    inference(superposition,[],[f47,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f243,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl8_9
    | spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f241,f118])).

fof(f241,plain,
    ( k1_xboole_0 = sK5
    | spl8_9
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f240,f114])).

fof(f240,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | ~ spl8_12 ),
    inference(superposition,[],[f27,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f237,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl8_13 ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_13 ),
    inference(superposition,[],[f22,f132])).

fof(f132,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f190,plain,
    ( spl8_14
    | spl8_13
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f189,f113,f131,f146])).

fof(f189,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f188,f25])).

fof(f188,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f182,f55])).

fof(f182,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_9 ),
    inference(superposition,[],[f47,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f176,f55])).

fof(f176,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f175,f55])).

fof(f175,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f174,f55])).

fof(f174,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f43,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f171,plain,
    ( spl8_14
    | spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f170,f121,f131,f146])).

fof(f170,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f169,f25])).

fof(f169,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f163,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_11 ),
    inference(superposition,[],[f47,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f160,f55])).

fof(f160,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f159,f54])).

fof(f159,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f43,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f149,plain,
    ( spl8_14
    | spl8_13
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f144,f82,f131,f146])).

fof(f144,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f143,f25])).

fof(f143,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f47,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f103,f54])).

fof(f103,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f43,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f75,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f26,f72,f68,f64,f60])).

fof(f26,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (6371)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6387)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (6390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (6367)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (6379)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (6373)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (6370)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (6382)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (6391)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (6379)Refutation not found, incomplete strategy% (6379)------------------------------
% 0.21/0.55  % (6379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6379)Memory used [KB]: 1663
% 0.21/0.55  % (6379)Time elapsed: 0.127 s
% 0.21/0.55  % (6379)------------------------------
% 0.21/0.55  % (6379)------------------------------
% 0.21/0.55  % (6366)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (6369)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (6371)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f843,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f75,f149,f171,f190,f237,f243,f406,f485,f501,f519,f713,f799,f840,f842])).
% 0.21/0.55  fof(f842,plain,(
% 0.21/0.55    spl8_4 | spl8_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f841])).
% 0.21/0.55  fof(f841,plain,(
% 0.21/0.55    $false | (spl8_4 | spl8_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f74,f272])).
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    sK3 = sK7 | spl8_7),
% 0.21/0.55    inference(equality_resolution,[],[f264])).
% 0.21/0.55  fof(f264,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2) ) | spl8_7),
% 0.21/0.55    inference(subsumption_resolution,[],[f256,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl8_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl8_7 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2) )),
% 0.21/0.55    inference(superposition,[],[f51,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.55    inference(definition_unfolding,[],[f21,f42,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f35,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 0.21/0.55    inference(definition_unfolding,[],[f41,f30,f30,f30])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    sK3 != sK7 | spl8_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    spl8_4 <=> sK3 = sK7),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.55  fof(f840,plain,(
% 0.21/0.55    spl8_3 | spl8_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f839])).
% 0.21/0.55  fof(f839,plain,(
% 0.21/0.55    $false | (spl8_3 | spl8_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f327,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    sK2 != sK6 | spl8_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl8_3 <=> sK2 = sK6),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.55  fof(f327,plain,(
% 0.21/0.55    sK2 = sK6 | spl8_7),
% 0.21/0.55    inference(equality_resolution,[],[f305])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) ) | spl8_7),
% 0.21/0.55    inference(subsumption_resolution,[],[f297,f92])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) ) | spl8_7),
% 0.21/0.55    inference(superposition,[],[f52,f276])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | spl8_7),
% 0.21/0.55    inference(backward_demodulation,[],[f43,f272])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f40,f30,f30,f30])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f799,plain,(
% 0.21/0.55    spl8_1 | spl8_5 | spl8_7 | spl8_9 | spl8_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f798])).
% 0.21/0.55  fof(f798,plain,(
% 0.21/0.55    $false | (spl8_1 | spl8_5 | spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f797])).
% 0.21/0.55  fof(f797,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | (spl8_1 | spl8_5 | spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(superposition,[],[f83,f759])).
% 0.21/0.55  fof(f759,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0) ) | (spl8_1 | spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f755,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    sK0 != sK4 | spl8_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    spl8_1 <=> sK0 = sK4),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.55  fof(f755,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | sK0 = sK4) ) | (spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(equality_resolution,[],[f692])).
% 0.21/0.55  fof(f692,plain,(
% 0.21/0.55    ( ! [X19,X17,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17) | k1_xboole_0 = X17 | sK4 = X18) ) | (spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f691,f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    k1_xboole_0 != sK4 | spl8_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f113])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl8_9 <=> k1_xboole_0 = sK4),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.55  fof(f691,plain,(
% 0.21/0.55    ( ! [X19,X17,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17) | k1_xboole_0 = X17 | k1_xboole_0 = sK4 | sK4 = X18) ) | (spl8_7 | spl8_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f677,f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    k1_xboole_0 != sK5 | spl8_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f117])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    spl8_10 <=> k1_xboole_0 = sK5),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.55  fof(f677,plain,(
% 0.21/0.55    ( ! [X19,X17,X20,X18] : (k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17) | k1_xboole_0 = X17 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK4 = X18) ) | spl8_7),
% 0.21/0.55    inference(superposition,[],[f50,f367])).
% 0.21/0.55  fof(f367,plain,(
% 0.21/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | spl8_7),
% 0.21/0.55    inference(equality_resolution,[],[f319])).
% 0.21/0.55  fof(f319,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0) ) | spl8_7),
% 0.21/0.55    inference(subsumption_resolution,[],[f311,f92])).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0) ) | spl8_7),
% 0.21/0.55    inference(superposition,[],[f53,f276])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f30,f30,f30])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f36,f30,f30])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  % (6376)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    k1_xboole_0 != sK7 | spl8_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl8_5 <=> k1_xboole_0 = sK7),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.55  fof(f713,plain,(
% 0.21/0.55    spl8_2 | spl8_13 | spl8_7 | spl8_9 | spl8_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f709,f117,f113,f90,f131,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl8_2 <=> sK1 = sK5),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    spl8_13 <=> ! [X0] : k1_xboole_0 = X0),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.55  fof(f709,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | sK1 = sK5) ) | (spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(equality_resolution,[],[f690])).
% 0.21/0.55  fof(f690,plain,(
% 0.21/0.55    ( ! [X12,X10,X11,X9] : (k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9) | k1_xboole_0 = X9 | sK5 = X11) ) | (spl8_7 | spl8_9 | spl8_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f689,f114])).
% 0.21/0.55  fof(f689,plain,(
% 0.21/0.55    ( ! [X12,X10,X11,X9] : (k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9) | k1_xboole_0 = X9 | k1_xboole_0 = sK4 | sK5 = X11) ) | (spl8_7 | spl8_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f675,f118])).
% 0.21/0.55  fof(f675,plain,(
% 0.21/0.55    ( ! [X12,X10,X11,X9] : (k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X9) | k1_xboole_0 = X9 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X11) ) | spl8_7),
% 0.21/0.55    inference(superposition,[],[f49,f367])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f37,f30,f30])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f519,plain,(
% 0.21/0.55    ~spl8_14),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f518])).
% 0.21/0.55  fof(f518,plain,(
% 0.21/0.55    $false | ~spl8_14),
% 0.21/0.55    inference(subsumption_resolution,[],[f517,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f517,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl8_14),
% 0.21/0.55    inference(subsumption_resolution,[],[f516,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f516,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_14),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f515])).
% 0.21/0.55  fof(f515,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_14),
% 0.21/0.55    inference(superposition,[],[f27,f513])).
% 0.21/0.55  fof(f513,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_14),
% 0.21/0.55    inference(subsumption_resolution,[],[f511,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_14),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f510])).
% 0.21/0.55  fof(f510,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_14),
% 0.21/0.55    inference(superposition,[],[f27,f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f146])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    spl8_14 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  fof(f501,plain,(
% 0.21/0.55    spl8_6 | ~spl8_7 | spl8_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f500,f82,f90,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl8_6 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.55  fof(f500,plain,(
% 0.21/0.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f499,f83])).
% 0.21/0.55  fof(f499,plain,(
% 0.21/0.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = sK7),
% 0.21/0.55    inference(superposition,[],[f27,f43])).
% 0.21/0.55  fof(f485,plain,(
% 0.21/0.55    ~spl8_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f484])).
% 0.21/0.55  fof(f484,plain,(
% 0.21/0.55    $false | ~spl8_10),
% 0.21/0.55    inference(subsumption_resolution,[],[f483,f23])).
% 0.21/0.55  fof(f483,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl8_10),
% 0.21/0.55    inference(subsumption_resolution,[],[f481,f22])).
% 0.21/0.55  fof(f481,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_10),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f480])).
% 0.21/0.55  fof(f480,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_10),
% 0.21/0.55    inference(superposition,[],[f27,f205])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_10),
% 0.21/0.55    inference(subsumption_resolution,[],[f204,f24])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_10),
% 0.21/0.55    inference(subsumption_resolution,[],[f203,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    k1_xboole_0 != sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_10),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f199])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_10),
% 0.21/0.55    inference(superposition,[],[f47,f196])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_10),
% 0.21/0.55    inference(forward_demodulation,[],[f195,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_10),
% 0.21/0.55    inference(forward_demodulation,[],[f194,f55])).
% 0.21/0.55  % (6392)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7) | ~spl8_10),
% 0.21/0.55    inference(forward_demodulation,[],[f193,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7) | ~spl8_10),
% 0.21/0.55    inference(forward_demodulation,[],[f43,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    k1_xboole_0 = sK5 | ~spl8_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f117])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f31,f30])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.21/0.55  fof(f406,plain,(
% 0.21/0.55    spl8_12 | spl8_13 | ~spl8_6 | spl8_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f405,f121,f86,f131,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    spl8_12 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    spl8_11 <=> k1_xboole_0 = sK6),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.55  fof(f405,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)) ) | (~spl8_6 | spl8_11)),
% 0.21/0.55    inference(subsumption_resolution,[],[f125,f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    k1_xboole_0 != sK6 | spl8_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f121])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)) ) | ~spl8_6),
% 0.21/0.55    inference(subsumption_resolution,[],[f108,f55])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)) ) | ~spl8_6),
% 0.21/0.55    inference(superposition,[],[f47,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f86])).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    spl8_9 | spl8_10 | ~spl8_12),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f242])).
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    $false | (spl8_9 | spl8_10 | ~spl8_12)),
% 0.21/0.55    inference(subsumption_resolution,[],[f241,f118])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    k1_xboole_0 = sK5 | (spl8_9 | ~spl8_12)),
% 0.21/0.55    inference(subsumption_resolution,[],[f240,f114])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    k1_xboole_0 = sK4 | k1_xboole_0 = sK5 | ~spl8_12),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f239])).
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 = sK5 | ~spl8_12),
% 0.21/0.55    inference(superposition,[],[f27,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f127])).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    ~spl8_13),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    $false | ~spl8_13),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f217])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | ~spl8_13),
% 0.21/0.55    inference(superposition,[],[f22,f132])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl8_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f131])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    spl8_14 | spl8_13 | ~spl8_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f189,f113,f131,f146])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f188,f25])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f182,f55])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_9),
% 0.21/0.55    inference(superposition,[],[f47,f177])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_9),
% 0.21/0.55    inference(forward_demodulation,[],[f176,f55])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_9),
% 0.21/0.55    inference(forward_demodulation,[],[f175,f55])).
% 0.21/0.55  fof(f175,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7) | ~spl8_9),
% 0.21/0.55    inference(forward_demodulation,[],[f174,f55])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7) | ~spl8_9),
% 0.21/0.55    inference(forward_demodulation,[],[f43,f115])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    k1_xboole_0 = sK4 | ~spl8_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f113])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    spl8_14 | spl8_13 | ~spl8_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f170,f121,f131,f146])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_11),
% 0.21/0.55    inference(subsumption_resolution,[],[f169,f25])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_11),
% 0.21/0.55    inference(subsumption_resolution,[],[f163,f55])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_11),
% 0.21/0.55    inference(superposition,[],[f47,f161])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_11),
% 0.21/0.55    inference(forward_demodulation,[],[f160,f55])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_11),
% 0.21/0.55    inference(forward_demodulation,[],[f159,f54])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7) | ~spl8_11),
% 0.21/0.55    inference(forward_demodulation,[],[f43,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    k1_xboole_0 = sK6 | ~spl8_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f121])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl8_14 | spl8_13 | ~spl8_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f144,f82,f131,f146])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f143,f25])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f137,f55])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) | ~spl8_5),
% 0.21/0.55    inference(superposition,[],[f47,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_5),
% 0.21/0.55    inference(forward_demodulation,[],[f103,f54])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0) | ~spl8_5),
% 0.21/0.55    inference(backward_demodulation,[],[f43,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    k1_xboole_0 = sK7 | ~spl8_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f26,f72,f68,f64,f60])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6371)------------------------------
% 0.21/0.55  % (6371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6368)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (6371)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6371)Memory used [KB]: 11001
% 0.21/0.55  % (6371)Time elapsed: 0.116 s
% 0.21/0.55  % (6371)------------------------------
% 0.21/0.55  % (6371)------------------------------
% 0.21/0.55  % (6365)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (6385)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (6364)Success in time 0.196 s
%------------------------------------------------------------------------------
