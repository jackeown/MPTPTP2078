%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 4.61s
% Output     : Refutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 114 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  314 ( 366 expanded)
%              Number of equality atoms :  143 ( 166 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f99,f330,f335,f343,f354])).

fof(f354,plain,
    ( spl4_2
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f351,f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f351,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f347,f112])).

fof(f112,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f109,f65])).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f109,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f347,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl4_8 ),
    inference(superposition,[],[f86,f342])).

fof(f342,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl4_8
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f343,plain,
    ( spl4_8
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f338,f90,f340])).

fof(f90,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f338,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f337,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f337,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f63,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f335,plain,
    ( ~ spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f332,f96])).

fof(f96,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f332,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(resolution,[],[f329,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f329,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_7
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f330,plain,
    ( ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f324,f90,f327])).

fof(f324,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f91,f316])).

fof(f316,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f311,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f311,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f64,f299])).

fof(f299,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f298,f196])).

fof(f196,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f192,f75])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f192,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f175,f101])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f75,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f175,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f73,f68])).

fof(f73,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f298,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f282,f75])).

fof(f282,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,X2),X2) = k3_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f74,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f98,f94,f90])).

fof(f98,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f46,f96])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f97,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f94,f90])).

fof(f45,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (8833)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (8836)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.51  % (8838)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.16/0.51  % (8854)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.16/0.52  % (8835)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.52  % (8848)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.16/0.52  % (8846)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.16/0.52  % (8846)Refutation not found, incomplete strategy% (8846)------------------------------
% 1.16/0.52  % (8846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (8846)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (8846)Memory used [KB]: 6140
% 1.16/0.52  % (8846)Time elapsed: 0.002 s
% 1.16/0.52  % (8846)------------------------------
% 1.16/0.52  % (8846)------------------------------
% 1.16/0.52  % (8860)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.16/0.52  % (8830)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.16/0.52  % (8837)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.16/0.52  % (8851)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.16/0.52  % (8857)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.16/0.53  % (8834)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.53  % (8840)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.16/0.53  % (8844)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.16/0.53  % (8843)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.53  % (8853)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.53  % (8832)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.53  % (8831)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.16/0.53  % (8859)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.53  % (8839)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (8858)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (8856)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (8848)Refutation not found, incomplete strategy% (8848)------------------------------
% 1.29/0.54  % (8848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (8848)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (8848)Memory used [KB]: 10618
% 1.29/0.54  % (8848)Time elapsed: 0.140 s
% 1.29/0.54  % (8848)------------------------------
% 1.29/0.54  % (8848)------------------------------
% 1.29/0.54  % (8849)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (8845)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (8855)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (8842)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (8850)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.56  % (8847)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.58  % (8852)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.01/0.65  % (8945)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.01/0.68  % (8960)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.47/0.84  % (8835)Time limit reached!
% 3.47/0.84  % (8835)------------------------------
% 3.47/0.84  % (8835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.84  % (8835)Termination reason: Time limit
% 3.47/0.84  % (8835)Termination phase: Saturation
% 3.47/0.84  
% 3.47/0.84  % (8835)Memory used [KB]: 10618
% 3.47/0.84  % (8835)Time elapsed: 0.400 s
% 3.47/0.84  % (8835)------------------------------
% 3.47/0.84  % (8835)------------------------------
% 3.47/0.92  % (8840)Time limit reached!
% 3.47/0.92  % (8840)------------------------------
% 3.47/0.92  % (8840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.92  % (8840)Termination reason: Time limit
% 3.47/0.92  
% 3.47/0.92  % (8840)Memory used [KB]: 14583
% 3.47/0.92  % (8840)Time elapsed: 0.512 s
% 3.47/0.92  % (8840)------------------------------
% 3.47/0.92  % (8840)------------------------------
% 4.15/0.93  % (8830)Time limit reached!
% 4.15/0.93  % (8830)------------------------------
% 4.15/0.93  % (8830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.94  % (8831)Time limit reached!
% 4.15/0.94  % (8831)------------------------------
% 4.15/0.94  % (8831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.94  % (8831)Termination reason: Time limit
% 4.15/0.94  
% 4.15/0.94  % (8831)Memory used [KB]: 9466
% 4.15/0.94  % (8831)Time elapsed: 0.530 s
% 4.15/0.94  % (8831)------------------------------
% 4.15/0.94  % (8831)------------------------------
% 4.15/0.94  % (8830)Termination reason: Time limit
% 4.15/0.94  
% 4.15/0.94  % (8830)Memory used [KB]: 2814
% 4.15/0.94  % (8830)Time elapsed: 0.524 s
% 4.15/0.94  % (8830)------------------------------
% 4.15/0.94  % (8830)------------------------------
% 4.15/0.94  % (8843)Time limit reached!
% 4.15/0.94  % (8843)------------------------------
% 4.15/0.94  % (8843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.94  % (8843)Termination reason: Time limit
% 4.15/0.94  
% 4.15/0.94  % (8843)Memory used [KB]: 13688
% 4.15/0.94  % (8843)Time elapsed: 0.540 s
% 4.15/0.94  % (8843)------------------------------
% 4.15/0.94  % (8843)------------------------------
% 4.15/0.98  % (9052)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.61/1.01  % (8847)Time limit reached!
% 4.61/1.01  % (8847)------------------------------
% 4.61/1.01  % (8847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.01  % (8847)Termination reason: Time limit
% 4.61/1.01  % (8847)Termination phase: Saturation
% 4.61/1.01  
% 4.61/1.01  % (8847)Memory used [KB]: 15991
% 4.61/1.01  % (8847)Time elapsed: 0.600 s
% 4.61/1.01  % (8847)------------------------------
% 4.61/1.01  % (8847)------------------------------
% 4.61/1.02  % (9053)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.61/1.03  % (8859)Time limit reached!
% 4.61/1.03  % (8859)------------------------------
% 4.61/1.03  % (8859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.04  % (9054)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.61/1.04  % (8859)Termination reason: Time limit
% 4.61/1.04  % (8859)Termination phase: Saturation
% 4.61/1.04  
% 4.61/1.04  % (8859)Memory used [KB]: 9210
% 4.61/1.04  % (8859)Time elapsed: 0.600 s
% 4.61/1.04  % (8859)------------------------------
% 4.61/1.04  % (8859)------------------------------
% 4.61/1.06  % (9054)Refutation found. Thanks to Tanya!
% 4.61/1.06  % SZS status Theorem for theBenchmark
% 4.61/1.06  % SZS output start Proof for theBenchmark
% 4.61/1.06  fof(f355,plain,(
% 4.61/1.06    $false),
% 4.61/1.06    inference(avatar_sat_refutation,[],[f97,f99,f330,f335,f343,f354])).
% 4.61/1.06  fof(f354,plain,(
% 4.61/1.06    spl4_2 | ~spl4_8),
% 4.61/1.06    inference(avatar_contradiction_clause,[],[f353])).
% 4.61/1.06  fof(f353,plain,(
% 4.61/1.06    $false | (spl4_2 | ~spl4_8)),
% 4.61/1.06    inference(subsumption_resolution,[],[f351,f95])).
% 4.61/1.06  fof(f95,plain,(
% 4.61/1.06    ~r2_hidden(sK0,sK1) | spl4_2),
% 4.61/1.06    inference(avatar_component_clause,[],[f94])).
% 4.61/1.06  fof(f94,plain,(
% 4.61/1.06    spl4_2 <=> r2_hidden(sK0,sK1)),
% 4.61/1.06    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.61/1.06  fof(f351,plain,(
% 4.61/1.06    r2_hidden(sK0,sK1) | ~spl4_8),
% 4.61/1.06    inference(resolution,[],[f347,f112])).
% 4.61/1.06  fof(f112,plain,(
% 4.61/1.06    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 4.61/1.06    inference(superposition,[],[f109,f65])).
% 4.61/1.06  fof(f65,plain,(
% 4.61/1.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f15])).
% 4.61/1.06  fof(f15,axiom,(
% 4.61/1.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.61/1.06  fof(f109,plain,(
% 4.61/1.06    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 4.61/1.06    inference(superposition,[],[f84,f70])).
% 4.61/1.06  fof(f70,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f16])).
% 4.61/1.06  fof(f16,axiom,(
% 4.61/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.61/1.06  fof(f84,plain,(
% 4.61/1.06    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 4.61/1.06    inference(equality_resolution,[],[f83])).
% 4.61/1.06  fof(f83,plain,(
% 4.61/1.06    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 4.61/1.06    inference(equality_resolution,[],[f48])).
% 4.61/1.06  fof(f48,plain,(
% 4.61/1.06    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.61/1.06    inference(cnf_transformation,[],[f38])).
% 4.61/1.06  fof(f38,plain,(
% 4.61/1.06    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 4.61/1.06  fof(f37,plain,(
% 4.61/1.06    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 4.61/1.06    introduced(choice_axiom,[])).
% 4.61/1.06  fof(f36,plain,(
% 4.61/1.06    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.61/1.06    inference(rectify,[],[f35])).
% 4.61/1.06  fof(f35,plain,(
% 4.61/1.06    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.61/1.06    inference(flattening,[],[f34])).
% 4.61/1.06  fof(f34,plain,(
% 4.61/1.06    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.61/1.06    inference(nnf_transformation,[],[f29])).
% 4.61/1.06  fof(f29,plain,(
% 4.61/1.06    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.61/1.06    inference(ennf_transformation,[],[f14])).
% 4.61/1.06  fof(f14,axiom,(
% 4.61/1.06    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 4.61/1.06  fof(f347,plain,(
% 4.61/1.06    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK0)) | r2_hidden(X1,sK1)) ) | ~spl4_8),
% 4.61/1.06    inference(superposition,[],[f86,f342])).
% 4.61/1.06  fof(f342,plain,(
% 4.61/1.06    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_8),
% 4.61/1.06    inference(avatar_component_clause,[],[f340])).
% 4.61/1.06  fof(f340,plain,(
% 4.61/1.06    spl4_8 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 4.61/1.06    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 4.61/1.06  fof(f86,plain,(
% 4.61/1.06    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 4.61/1.06    inference(equality_resolution,[],[f57])).
% 4.61/1.06  fof(f57,plain,(
% 4.61/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 4.61/1.06    inference(cnf_transformation,[],[f43])).
% 4.61/1.06  fof(f43,plain,(
% 4.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 4.61/1.06  fof(f42,plain,(
% 4.61/1.06    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 4.61/1.06    introduced(choice_axiom,[])).
% 4.61/1.06  fof(f41,plain,(
% 4.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.61/1.06    inference(rectify,[],[f40])).
% 4.61/1.06  fof(f40,plain,(
% 4.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.61/1.06    inference(flattening,[],[f39])).
% 4.61/1.06  fof(f39,plain,(
% 4.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.61/1.06    inference(nnf_transformation,[],[f2])).
% 4.61/1.06  fof(f2,axiom,(
% 4.61/1.06    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.61/1.06  fof(f343,plain,(
% 4.61/1.06    spl4_8 | ~spl4_1),
% 4.61/1.06    inference(avatar_split_clause,[],[f338,f90,f340])).
% 4.61/1.06  fof(f90,plain,(
% 4.61/1.06    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 4.61/1.06    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.61/1.06  fof(f338,plain,(
% 4.61/1.06    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_1),
% 4.61/1.06    inference(forward_demodulation,[],[f337,f67])).
% 4.61/1.06  fof(f67,plain,(
% 4.61/1.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.61/1.06    inference(cnf_transformation,[],[f7])).
% 4.61/1.06  fof(f7,axiom,(
% 4.61/1.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 4.61/1.06  fof(f337,plain,(
% 4.61/1.06    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_1),
% 4.61/1.06    inference(superposition,[],[f63,f92])).
% 4.61/1.06  fof(f92,plain,(
% 4.61/1.06    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 4.61/1.06    inference(avatar_component_clause,[],[f90])).
% 4.61/1.06  fof(f63,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.61/1.06    inference(cnf_transformation,[],[f8])).
% 4.61/1.06  fof(f8,axiom,(
% 4.61/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.61/1.06  fof(f335,plain,(
% 4.61/1.06    ~spl4_2 | spl4_7),
% 4.61/1.06    inference(avatar_contradiction_clause,[],[f334])).
% 4.61/1.06  fof(f334,plain,(
% 4.61/1.06    $false | (~spl4_2 | spl4_7)),
% 4.61/1.06    inference(subsumption_resolution,[],[f332,f96])).
% 4.61/1.06  fof(f96,plain,(
% 4.61/1.06    r2_hidden(sK0,sK1) | ~spl4_2),
% 4.61/1.06    inference(avatar_component_clause,[],[f94])).
% 4.61/1.06  fof(f332,plain,(
% 4.61/1.06    ~r2_hidden(sK0,sK1) | spl4_7),
% 4.61/1.06    inference(resolution,[],[f329,f62])).
% 4.61/1.06  fof(f62,plain,(
% 4.61/1.06    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f44])).
% 4.61/1.06  fof(f44,plain,(
% 4.61/1.06    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 4.61/1.06    inference(nnf_transformation,[],[f22])).
% 4.61/1.06  fof(f22,axiom,(
% 4.61/1.06    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 4.61/1.06  fof(f329,plain,(
% 4.61/1.06    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_7),
% 4.61/1.06    inference(avatar_component_clause,[],[f327])).
% 4.61/1.06  fof(f327,plain,(
% 4.61/1.06    spl4_7 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 4.61/1.06    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 4.61/1.06  fof(f330,plain,(
% 4.61/1.06    ~spl4_7 | spl4_1),
% 4.61/1.06    inference(avatar_split_clause,[],[f324,f90,f327])).
% 4.61/1.06  fof(f324,plain,(
% 4.61/1.06    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 4.61/1.06    inference(trivial_inequality_removal,[],[f319])).
% 4.61/1.06  fof(f319,plain,(
% 4.61/1.06    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 4.61/1.06    inference(superposition,[],[f91,f316])).
% 4.61/1.06  fof(f316,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 4.61/1.06    inference(forward_demodulation,[],[f311,f68])).
% 4.61/1.06  fof(f68,plain,(
% 4.61/1.06    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f11])).
% 4.61/1.06  fof(f11,axiom,(
% 4.61/1.06    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.61/1.06  fof(f311,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 4.61/1.06    inference(superposition,[],[f64,f299])).
% 4.61/1.06  fof(f299,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 4.61/1.06    inference(forward_demodulation,[],[f298,f196])).
% 4.61/1.06  fof(f196,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.61/1.06    inference(superposition,[],[f192,f75])).
% 4.61/1.06  fof(f75,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f1])).
% 4.61/1.06  fof(f1,axiom,(
% 4.61/1.06    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.61/1.06  fof(f192,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.61/1.06    inference(forward_demodulation,[],[f175,f101])).
% 4.61/1.06  fof(f101,plain,(
% 4.61/1.06    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.61/1.06    inference(superposition,[],[f75,f66])).
% 4.61/1.06  fof(f66,plain,(
% 4.61/1.06    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.61/1.06    inference(cnf_transformation,[],[f9])).
% 4.61/1.06  fof(f9,axiom,(
% 4.61/1.06    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 4.61/1.06  fof(f175,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.61/1.06    inference(superposition,[],[f73,f68])).
% 4.61/1.06  fof(f73,plain,(
% 4.61/1.06    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.61/1.06    inference(cnf_transformation,[],[f10])).
% 4.61/1.06  fof(f10,axiom,(
% 4.61/1.06    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.61/1.06  fof(f298,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 4.61/1.06    inference(forward_demodulation,[],[f282,f75])).
% 4.61/1.06  fof(f282,plain,(
% 4.61/1.06    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),X2) = k3_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 4.61/1.06    inference(superposition,[],[f74,f72])).
% 4.61/1.06  fof(f72,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.61/1.06    inference(cnf_transformation,[],[f30])).
% 4.61/1.06  fof(f30,plain,(
% 4.61/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.61/1.06    inference(ennf_transformation,[],[f6])).
% 4.61/1.06  fof(f6,axiom,(
% 4.61/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.61/1.06  fof(f74,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.61/1.06    inference(cnf_transformation,[],[f12])).
% 4.61/1.06  fof(f12,axiom,(
% 4.61/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.61/1.06  fof(f64,plain,(
% 4.61/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.61/1.06    inference(cnf_transformation,[],[f5])).
% 4.61/1.06  fof(f5,axiom,(
% 4.61/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.61/1.06  fof(f91,plain,(
% 4.61/1.06    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 4.61/1.06    inference(avatar_component_clause,[],[f90])).
% 4.61/1.06  fof(f99,plain,(
% 4.61/1.06    ~spl4_1 | ~spl4_2),
% 4.61/1.06    inference(avatar_split_clause,[],[f98,f94,f90])).
% 4.61/1.06  fof(f98,plain,(
% 4.61/1.06    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_2),
% 4.61/1.06    inference(subsumption_resolution,[],[f46,f96])).
% 4.61/1.06  fof(f46,plain,(
% 4.61/1.06    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 4.61/1.06    inference(cnf_transformation,[],[f33])).
% 4.61/1.06  fof(f33,plain,(
% 4.61/1.06    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 4.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 4.61/1.06  fof(f32,plain,(
% 4.61/1.06    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 4.61/1.06    introduced(choice_axiom,[])).
% 4.61/1.06  fof(f31,plain,(
% 4.61/1.06    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 4.61/1.06    inference(nnf_transformation,[],[f28])).
% 4.61/1.06  fof(f28,plain,(
% 4.61/1.06    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 4.61/1.06    inference(ennf_transformation,[],[f25])).
% 4.61/1.06  fof(f25,negated_conjecture,(
% 4.61/1.06    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.61/1.06    inference(negated_conjecture,[],[f24])).
% 4.61/1.06  fof(f24,conjecture,(
% 4.61/1.06    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 4.61/1.06  fof(f97,plain,(
% 4.61/1.06    spl4_1 | spl4_2),
% 4.61/1.06    inference(avatar_split_clause,[],[f45,f94,f90])).
% 4.61/1.06  fof(f45,plain,(
% 4.61/1.06    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 4.61/1.06    inference(cnf_transformation,[],[f33])).
% 4.61/1.06  % SZS output end Proof for theBenchmark
% 4.61/1.06  % (9054)------------------------------
% 4.61/1.06  % (9054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.06  % (9054)Termination reason: Refutation
% 4.61/1.06  
% 4.61/1.06  % (9054)Memory used [KB]: 10874
% 4.61/1.06  % (9054)Time elapsed: 0.070 s
% 4.61/1.06  % (9054)------------------------------
% 4.61/1.06  % (9054)------------------------------
% 5.05/1.06  % (8827)Success in time 0.697 s
%------------------------------------------------------------------------------
