%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 210 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  473 (1367 expanded)
%              Number of equality atoms :  325 (1088 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f195,f279,f286,f288,f298,f320,f323,f327])).

fof(f327,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f138,f282])).

fof(f282,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl6_9
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f138,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f32])).

% (11807)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f323,plain,
    ( ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f278,f285])).

fof(f285,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl6_10
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f278,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl6_8
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f320,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_7 ),
    inference(superposition,[],[f307,f301])).

fof(f301,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f58,f275])).

fof(f275,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,X1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl6_7
  <=> ! [X1,X0] : r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f307,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f53,f301])).

fof(f53,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f298,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f289,f179])).

fof(f179,plain,
    ( ! [X5] : sK2 = X5
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_1
  <=> ! [X5] : sK2 = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f289,plain,
    ( sK0 != sK2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f53,f194])).

fof(f194,plain,
    ( sK0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f288,plain,
    ( ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f198,f194])).

fof(f198,plain,
    ( sK0 != sK1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f53,f182])).

fof(f182,plain,
    ( sK0 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f286,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f251,f190,f284,f281])).

fof(f190,plain,
    ( spl6_3
  <=> ! [X5] : sK1 = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f112,f191])).

fof(f191,plain,
    ( ! [X5] : sK1 = X5
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f190])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f279,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f272,f190,f277,f274])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1,sK1)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f250,f191])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),sK1)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f113,f191])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f195,plain,
    ( spl6_3
    | spl6_4
    | spl6_3
    | spl6_3
    | spl6_3
    | spl6_3
    | spl6_3 ),
    inference(avatar_split_clause,[],[f188,f190,f190,f190,f190,f190,f193,f190])).

fof(f188,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK0 = sK1
      | sK1 = X5 ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK1 = X5 ) ),
    inference(resolution,[],[f168,f157])).

fof(f157,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] :
      ( ~ r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))))
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | X8 = X11 ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9 ) ),
    inference(definition_unfolding,[],[f82,f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f81,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 )
            | ~ r2_hidden(X10,X9) )
          & ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10
            | r2_hidden(X10,X9) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f168,plain,(
    ! [X52,X50,X48,X53,X51,X49] : r2_hidden(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k4_enumset1(X48,X49,X50,X51,X52,X53),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(superposition,[],[f154,f106])).

fof(f106,plain,(
    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f52,f104,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f104,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f154,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X11,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X11,X2)))) ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] :
      ( r2_hidden(X11,X9)
      | k5_xboole_0(k1_enumset1(X0,X11,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X11,X2))) != X9 ) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9 ) ),
    inference(definition_unfolding,[],[f84,f102])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f183,plain,
    ( spl6_1
    | spl6_2
    | spl6_1
    | spl6_1
    | spl6_1
    | spl6_1
    | spl6_1 ),
    inference(avatar_split_clause,[],[f176,f178,f178,f178,f178,f178,f181,f178])).

fof(f176,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK2 = X0
      | sK2 = X1
      | sK2 = X2
      | sK2 = X3
      | sK2 = X4
      | sK0 = sK2
      | sK2 = X5 ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK2 = X0
      | sK2 = X1
      | sK2 = X2
      | sK2 = X3
      | sK2 = X4
      | sK0 = sK2
      | sK0 = sK2
      | sK0 = sK2
      | sK2 = X5 ) ),
    inference(resolution,[],[f167,f157])).

fof(f167,plain,(
    ! [X47,X45,X43,X46,X44,X42] : r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k4_enumset1(X42,X43,X44,X45,X46,X47),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(superposition,[],[f152,f106])).

fof(f152,plain,(
    ! [X6,X4,X0,X8,X7,X5,X3,X1,X11] : r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X1,X11),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X11)))) ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,(
    ! [X6,X4,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | k5_xboole_0(k1_enumset1(X0,X1,X11),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X11))) != X9 ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X2 != X11
      | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9 ) ),
    inference(definition_unfolding,[],[f85,f102])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X2 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:30:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.51  % (11808)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11817)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (11809)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (11808)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11825)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (11832)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (11818)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11811)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (11817)Refutation not found, incomplete strategy% (11817)------------------------------
% 0.21/0.53  % (11817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11817)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11817)Memory used [KB]: 10618
% 0.21/0.53  % (11817)Time elapsed: 0.115 s
% 0.21/0.53  % (11817)------------------------------
% 0.21/0.53  % (11817)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f183,f195,f279,f286,f288,f298,f320,f323,f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    ~spl6_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f325])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    $false | ~spl6_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f282])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl6_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    spl6_9 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    inference(equality_resolution,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  % (11807)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    ~spl6_8 | ~spl6_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f322])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    $false | (~spl6_8 | ~spl6_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f278,f285])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl6_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f284])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    spl6_10 <=> ! [X2] : ~r2_hidden(X2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    r2_hidden(sK1,sK1) | ~spl6_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f277])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    spl6_8 <=> r2_hidden(sK1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    ~spl6_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f319])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    $false | ~spl6_7),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f317])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~spl6_7),
% 0.21/0.53    inference(superposition,[],[f307,f301])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f58,f275])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1)) ) | ~spl6_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    spl6_7 <=> ! [X1,X0] : r1_xboole_0(X0,X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | ~spl6_7),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f301])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    sK1 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.53    inference(negated_conjecture,[],[f26])).
% 0.21/0.53  fof(f26,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ~spl6_1 | ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    $false | (~spl6_1 | ~spl6_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X5] : (sK2 = X5) ) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl6_1 <=> ! [X5] : sK2 = X5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    sK0 != sK2 | ~spl6_4),
% 0.21/0.53    inference(forward_demodulation,[],[f53,f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    sK0 = sK1 | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl6_4 <=> sK0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ~spl6_2 | ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    $false | (~spl6_2 | ~spl6_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f198,f194])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    sK0 != sK1 | ~spl6_2),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f182])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    sK0 = sK2 | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f181])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl6_2 <=> sK0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    spl6_9 | spl6_10 | ~spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f251,f190,f284,f281])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    spl6_3 <=> ! [X5] : sK1 = X5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK1) | ~r1_xboole_0(X0,X1)) ) | ~spl6_3),
% 0.21/0.53    inference(backward_demodulation,[],[f112,f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ( ! [X5] : (sK1 = X5) ) | ~spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f190])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f68,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    spl6_7 | spl6_8 | ~spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f272,f190,f277,f274])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK1,sK1) | r1_xboole_0(X0,X1)) ) | ~spl6_3),
% 0.21/0.53    inference(forward_demodulation,[],[f250,f191])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),sK1) | r1_xboole_0(X0,X1)) ) | ~spl6_3),
% 0.21/0.53    inference(backward_demodulation,[],[f113,f191])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f67,f63])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl6_3 | spl6_4 | spl6_3 | spl6_3 | spl6_3 | spl6_3 | spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f188,f190,f190,f190,f190,f190,f193,f190])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK0 = sK1 | sK1 = X5) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK1 = X5) )),
% 0.21/0.53    inference(resolution,[],[f168,f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] : (~r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | X8 = X11) )),
% 0.21/0.53    inference(equality_resolution,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f82,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f81,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9))) => (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(rectify,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(flattening,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(nnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X52,X50,X48,X53,X51,X49] : (r2_hidden(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k4_enumset1(X48,X49,X50,X51,X52,X53),k1_enumset1(sK0,sK0,sK0))))) )),
% 0.21/0.53    inference(superposition,[],[f154,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f104,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f56,f62])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : (r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X11,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X11,X2))))) )),
% 0.21/0.53    inference(equality_resolution,[],[f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] : (r2_hidden(X11,X9) | k5_xboole_0(k1_enumset1(X0,X11,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X11,X2))) != X9) )),
% 0.21/0.53    inference(equality_resolution,[],[f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f84,f102])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f51])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl6_1 | spl6_2 | spl6_1 | spl6_1 | spl6_1 | spl6_1 | spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f176,f178,f178,f178,f178,f178,f181,f178])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK2 = X0 | sK2 = X1 | sK2 = X2 | sK2 = X3 | sK2 = X4 | sK0 = sK2 | sK2 = X5) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK2 = X0 | sK2 = X1 | sK2 = X2 | sK2 = X3 | sK2 = X4 | sK0 = sK2 | sK0 = sK2 | sK0 = sK2 | sK2 = X5) )),
% 0.21/0.53    inference(resolution,[],[f167,f157])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X47,X45,X43,X46,X44,X42] : (r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k4_enumset1(X42,X43,X44,X45,X46,X47),k1_enumset1(sK0,sK0,sK0))))) )),
% 0.21/0.53    inference(superposition,[],[f152,f106])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ( ! [X6,X4,X0,X8,X7,X5,X3,X1,X11] : (r2_hidden(X11,k5_xboole_0(k1_enumset1(X0,X1,X11),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X11))))) )),
% 0.21/0.53    inference(equality_resolution,[],[f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X6,X4,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | k5_xboole_0(k1_enumset1(X0,X1,X11),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X11))) != X9) )),
% 0.21/0.53    inference(equality_resolution,[],[f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X2 != X11 | k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f85,f102])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X2 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f51])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11808)------------------------------
% 0.21/0.53  % (11808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11808)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11808)Memory used [KB]: 10874
% 0.21/0.53  % (11808)Time elapsed: 0.107 s
% 0.21/0.53  % (11808)------------------------------
% 0.21/0.53  % (11808)------------------------------
% 0.21/0.53  % (11824)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (11805)Success in time 0.169 s
%------------------------------------------------------------------------------
