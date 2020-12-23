%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 359 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  391 (1279 expanded)
%              Number of equality atoms :   53 ( 288 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f569,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f94,f96,f116,f126,f136,f157,f162,f324,f331,f340,f355,f386,f392,f442,f449,f468,f490,f496,f561,f568])).

fof(f568,plain,
    ( ~ spl12_2
    | spl12_8
    | ~ spl12_31 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl12_2
    | spl12_8
    | ~ spl12_31 ),
    inference(resolution,[],[f562,f150])).

fof(f150,plain,
    ( r2_hidden(sK6(sK2,k1_xboole_0),sK2)
    | spl12_8 ),
    inference(resolution,[],[f124,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f124,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl12_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl12_8
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f562,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK2)
    | ~ spl12_2
    | ~ spl12_31 ),
    inference(forward_demodulation,[],[f448,f81])).

fof(f81,plain,
    ( sK2 = sK4
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl12_2
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f448,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK4)
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl12_31
  <=> ! [X6] : ~ r2_hidden(X6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f561,plain,
    ( spl12_10
    | ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | spl12_10
    | ~ spl12_30 ),
    inference(resolution,[],[f547,f134])).

fof(f134,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl12_10
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f547,plain,
    ( r1_tarski(sK3,sK1)
    | spl12_10
    | ~ spl12_30 ),
    inference(resolution,[],[f475,f152])).

fof(f152,plain,
    ( r2_hidden(sK6(sK3,sK1),sK3)
    | spl12_10 ),
    inference(resolution,[],[f134,f51])).

fof(f475,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK1),sK3)
        | r1_tarski(X3,sK1) )
    | ~ spl12_30 ),
    inference(resolution,[],[f445,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f445,plain,
    ( ! [X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(X7,sK3) )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl12_30
  <=> ! [X7] :
        ( ~ r2_hidden(X7,sK3)
        | r2_hidden(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f496,plain,
    ( ~ spl12_12
    | spl12_2
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f367,f138,f80,f142])).

fof(f142,plain,
    ( spl12_12
  <=> r1_tarski(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f138,plain,
    ( spl12_11
  <=> r1_tarski(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f367,plain,
    ( sK2 = sK4
    | ~ r1_tarski(sK4,sK2)
    | ~ spl12_11 ),
    inference(resolution,[],[f139,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,
    ( r1_tarski(sK2,sK4)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f490,plain,
    ( spl12_12
    | ~ spl12_29 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | spl12_12
    | ~ spl12_29 ),
    inference(resolution,[],[f476,f144])).

fof(f144,plain,
    ( ~ r1_tarski(sK4,sK2)
    | spl12_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f476,plain,
    ( r1_tarski(sK4,sK2)
    | spl12_12
    | ~ spl12_29 ),
    inference(resolution,[],[f472,f154])).

fof(f154,plain,
    ( r2_hidden(sK6(sK4,sK2),sK4)
    | spl12_12 ),
    inference(resolution,[],[f144,f51])).

fof(f472,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK2),sK4)
        | r1_tarski(X3,sK2) )
    | ~ spl12_29 ),
    inference(resolution,[],[f441,f52])).

fof(f441,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK2)
        | ~ r2_hidden(X4,sK4) )
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl12_29
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK4)
        | r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f468,plain,
    ( spl12_6
    | ~ spl12_9
    | ~ spl12_28 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl12_6
    | ~ spl12_9
    | ~ spl12_28 ),
    inference(resolution,[],[f438,f394])).

fof(f394,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),sK3)
    | spl12_6
    | ~ spl12_9 ),
    inference(resolution,[],[f129,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK6(sK1,k1_xboole_0),X0) )
    | spl12_6 ),
    inference(resolution,[],[f148,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),sK1)
    | spl12_6 ),
    inference(resolution,[],[f114,f51])).

fof(f114,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_6
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f129,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl12_9
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f438,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK3)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl12_28
  <=> ! [X5] : ~ r2_hidden(X5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f449,plain,
    ( spl12_30
    | spl12_31 ),
    inference(avatar_split_clause,[],[f434,f447,f444])).

fof(f434,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X7,sK3)
      | r2_hidden(X7,sK1) ) ),
    inference(resolution,[],[f315,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f315,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f68,f39])).

fof(f39,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK2 != sK4
      | sK1 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK2 != sK4
        | sK1 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f442,plain,
    ( spl12_28
    | spl12_29 ),
    inference(avatar_split_clause,[],[f433,f440,f437])).

fof(f433,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(X5,sK3)
      | r2_hidden(X4,sK2) ) ),
    inference(resolution,[],[f315,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f392,plain,
    ( spl12_8
    | ~ spl12_25 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl12_8
    | ~ spl12_25 ),
    inference(resolution,[],[f330,f150])).

fof(f330,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK2)
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl12_25
  <=> ! [X10] : ~ r2_hidden(X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f386,plain,
    ( spl12_9
    | ~ spl12_24 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl12_9
    | ~ spl12_24 ),
    inference(resolution,[],[f376,f130])).

fof(f130,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl12_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f376,plain,
    ( r1_tarski(sK1,sK3)
    | spl12_9
    | ~ spl12_24 ),
    inference(resolution,[],[f344,f151])).

fof(f151,plain,
    ( r2_hidden(sK6(sK1,sK3),sK1)
    | spl12_9 ),
    inference(resolution,[],[f130,f51])).

fof(f344,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(X2,sK3),sK1)
        | r1_tarski(X2,sK3) )
    | ~ spl12_24 ),
    inference(resolution,[],[f327,f52])).

fof(f327,plain,
    ( ! [X11] :
        ( r2_hidden(X11,sK3)
        | ~ r2_hidden(X11,sK1) )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl12_24
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK1)
        | r2_hidden(X11,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f355,plain,
    ( spl12_11
    | ~ spl12_23 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl12_11
    | ~ spl12_23 ),
    inference(resolution,[],[f345,f140])).

fof(f140,plain,
    ( ~ r1_tarski(sK2,sK4)
    | spl12_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f345,plain,
    ( r1_tarski(sK2,sK4)
    | spl12_11
    | ~ spl12_23 ),
    inference(resolution,[],[f342,f153])).

fof(f153,plain,
    ( r2_hidden(sK6(sK2,sK4),sK2)
    | spl12_11 ),
    inference(resolution,[],[f140,f51])).

fof(f342,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(X2,sK4),sK2)
        | r1_tarski(X2,sK4) )
    | ~ spl12_23 ),
    inference(resolution,[],[f323,f52])).

fof(f323,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK4)
        | ~ r2_hidden(X8,sK2) )
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl12_23
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK2)
        | r2_hidden(X8,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f340,plain,
    ( spl12_6
    | ~ spl12_22 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl12_6
    | ~ spl12_22 ),
    inference(resolution,[],[f320,f148])).

fof(f320,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK1)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl12_22
  <=> ! [X9] : ~ r2_hidden(X9,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f331,plain,
    ( spl12_24
    | spl12_25 ),
    inference(avatar_split_clause,[],[f313,f329,f326])).

fof(f313,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,sK2)
      | ~ r2_hidden(X11,sK1)
      | r2_hidden(X11,sK3) ) ),
    inference(resolution,[],[f68,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f66,f39])).

fof(f324,plain,
    ( spl12_22
    | spl12_23 ),
    inference(avatar_split_clause,[],[f312,f322,f319])).

fof(f312,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK2)
      | ~ r2_hidden(X9,sK1)
      | r2_hidden(X8,sK4) ) ),
    inference(resolution,[],[f68,f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X1,sK4) ) ),
    inference(superposition,[],[f67,f39])).

fof(f162,plain,
    ( ~ spl12_4
    | spl12_7 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl12_4
    | spl12_7 ),
    inference(resolution,[],[f149,f93])).

fof(f93,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl12_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f149,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k1_xboole_0)
    | spl12_7 ),
    inference(resolution,[],[f120,f51])).

fof(f120,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl12_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl12_7
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f157,plain,
    ( ~ spl12_4
    | spl12_5 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl12_4
    | spl12_5 ),
    inference(resolution,[],[f147,f93])).

fof(f147,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK1),k1_xboole_0)
    | spl12_5 ),
    inference(resolution,[],[f110,f51])).

fof(f110,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl12_5
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f136,plain,
    ( ~ spl12_10
    | ~ spl12_9
    | spl12_1 ),
    inference(avatar_split_clause,[],[f102,f76,f128,f132])).

fof(f76,plain,
    ( spl12_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f102,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK3,sK1)
    | spl12_1 ),
    inference(extensionality_resolution,[],[f49,f78])).

fof(f78,plain,
    ( sK1 != sK3
    | spl12_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f126,plain,
    ( ~ spl12_8
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f100,f118,f122])).

fof(f100,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(extensionality_resolution,[],[f49,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( ~ spl12_6
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f98,f108,f112])).

fof(f98,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(extensionality_resolution,[],[f49,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl12_3 ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f90,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl12_3
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f94,plain,
    ( spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f87,f92,f89])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f46,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f83,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f42,f80,f76])).

fof(f42,plain,
    ( sK2 != sK4
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17033)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (17057)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (17049)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (17037)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (17041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (17053)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (17045)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (17038)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.22/0.51  % (17032)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.52  % (17054)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.52  % (17045)Refutation not found, incomplete strategy% (17045)------------------------------
% 1.22/0.52  % (17045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (17045)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (17045)Memory used [KB]: 10618
% 1.22/0.52  % (17045)Time elapsed: 0.118 s
% 1.22/0.52  % (17045)------------------------------
% 1.22/0.52  % (17045)------------------------------
% 1.22/0.52  % (17031)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.52  % (17029)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (17050)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (17036)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.52  % (17040)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (17042)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (17030)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % (17034)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (17028)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.53  % (17056)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.53  % (17048)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.53  % (17051)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.53  % (17052)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.53  % (17055)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.54  % (17043)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.54  % (17028)Refutation not found, incomplete strategy% (17028)------------------------------
% 1.37/0.54  % (17028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (17047)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (17035)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.54  % (17028)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (17028)Memory used [KB]: 1663
% 1.37/0.54  % (17028)Time elapsed: 0.135 s
% 1.37/0.54  % (17028)------------------------------
% 1.37/0.54  % (17028)------------------------------
% 1.37/0.54  % (17044)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.54  % (17040)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.55  % (17039)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.57  % SZS output start Proof for theBenchmark
% 1.37/0.57  fof(f569,plain,(
% 1.37/0.57    $false),
% 1.37/0.57    inference(avatar_sat_refutation,[],[f83,f94,f96,f116,f126,f136,f157,f162,f324,f331,f340,f355,f386,f392,f442,f449,f468,f490,f496,f561,f568])).
% 1.37/0.57  fof(f568,plain,(
% 1.37/0.57    ~spl12_2 | spl12_8 | ~spl12_31),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f565])).
% 1.37/0.57  fof(f565,plain,(
% 1.37/0.57    $false | (~spl12_2 | spl12_8 | ~spl12_31)),
% 1.37/0.57    inference(resolution,[],[f562,f150])).
% 1.37/0.57  fof(f150,plain,(
% 1.37/0.57    r2_hidden(sK6(sK2,k1_xboole_0),sK2) | spl12_8),
% 1.37/0.57    inference(resolution,[],[f124,f51])).
% 1.37/0.57  fof(f51,plain,(
% 1.37/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f27])).
% 1.37/0.57  fof(f27,plain,(
% 1.37/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 1.37/0.57  fof(f26,plain,(
% 1.37/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.37/0.57    introduced(choice_axiom,[])).
% 1.37/0.57  fof(f25,plain,(
% 1.37/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.57    inference(rectify,[],[f24])).
% 1.37/0.57  fof(f24,plain,(
% 1.37/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.57    inference(nnf_transformation,[],[f15])).
% 1.37/0.57  fof(f15,plain,(
% 1.37/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.37/0.57    inference(ennf_transformation,[],[f1])).
% 1.37/0.57  fof(f1,axiom,(
% 1.37/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.37/0.57  fof(f124,plain,(
% 1.37/0.57    ~r1_tarski(sK2,k1_xboole_0) | spl12_8),
% 1.37/0.57    inference(avatar_component_clause,[],[f122])).
% 1.37/0.57  fof(f122,plain,(
% 1.37/0.57    spl12_8 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.37/0.57  fof(f562,plain,(
% 1.37/0.57    ( ! [X6] : (~r2_hidden(X6,sK2)) ) | (~spl12_2 | ~spl12_31)),
% 1.37/0.57    inference(forward_demodulation,[],[f448,f81])).
% 1.37/0.57  fof(f81,plain,(
% 1.37/0.57    sK2 = sK4 | ~spl12_2),
% 1.37/0.57    inference(avatar_component_clause,[],[f80])).
% 1.37/0.57  fof(f80,plain,(
% 1.37/0.57    spl12_2 <=> sK2 = sK4),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.37/0.57  fof(f448,plain,(
% 1.37/0.57    ( ! [X6] : (~r2_hidden(X6,sK4)) ) | ~spl12_31),
% 1.37/0.57    inference(avatar_component_clause,[],[f447])).
% 1.37/0.57  fof(f447,plain,(
% 1.37/0.57    spl12_31 <=> ! [X6] : ~r2_hidden(X6,sK4)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 1.37/0.57  fof(f561,plain,(
% 1.37/0.57    spl12_10 | ~spl12_30),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f554])).
% 1.37/0.57  fof(f554,plain,(
% 1.37/0.57    $false | (spl12_10 | ~spl12_30)),
% 1.37/0.57    inference(resolution,[],[f547,f134])).
% 1.37/0.57  fof(f134,plain,(
% 1.37/0.57    ~r1_tarski(sK3,sK1) | spl12_10),
% 1.37/0.57    inference(avatar_component_clause,[],[f132])).
% 1.37/0.57  fof(f132,plain,(
% 1.37/0.57    spl12_10 <=> r1_tarski(sK3,sK1)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.37/0.57  fof(f547,plain,(
% 1.37/0.57    r1_tarski(sK3,sK1) | (spl12_10 | ~spl12_30)),
% 1.37/0.57    inference(resolution,[],[f475,f152])).
% 1.37/0.57  fof(f152,plain,(
% 1.37/0.57    r2_hidden(sK6(sK3,sK1),sK3) | spl12_10),
% 1.37/0.57    inference(resolution,[],[f134,f51])).
% 1.37/0.57  fof(f475,plain,(
% 1.37/0.57    ( ! [X3] : (~r2_hidden(sK6(X3,sK1),sK3) | r1_tarski(X3,sK1)) ) | ~spl12_30),
% 1.37/0.57    inference(resolution,[],[f445,f52])).
% 1.37/0.57  fof(f52,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f27])).
% 1.37/0.57  fof(f445,plain,(
% 1.37/0.57    ( ! [X7] : (r2_hidden(X7,sK1) | ~r2_hidden(X7,sK3)) ) | ~spl12_30),
% 1.37/0.57    inference(avatar_component_clause,[],[f444])).
% 1.37/0.57  fof(f444,plain,(
% 1.37/0.57    spl12_30 <=> ! [X7] : (~r2_hidden(X7,sK3) | r2_hidden(X7,sK1))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 1.37/0.57  fof(f496,plain,(
% 1.37/0.57    ~spl12_12 | spl12_2 | ~spl12_11),
% 1.37/0.57    inference(avatar_split_clause,[],[f367,f138,f80,f142])).
% 1.37/0.57  fof(f142,plain,(
% 1.37/0.57    spl12_12 <=> r1_tarski(sK4,sK2)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.37/0.57  fof(f138,plain,(
% 1.37/0.57    spl12_11 <=> r1_tarski(sK2,sK4)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.37/0.57  fof(f367,plain,(
% 1.37/0.57    sK2 = sK4 | ~r1_tarski(sK4,sK2) | ~spl12_11),
% 1.37/0.57    inference(resolution,[],[f139,f49])).
% 1.37/0.57  fof(f49,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f23])).
% 1.37/0.57  fof(f23,plain,(
% 1.37/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.57    inference(flattening,[],[f22])).
% 1.37/0.57  fof(f22,plain,(
% 1.37/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.57    inference(nnf_transformation,[],[f3])).
% 1.37/0.57  fof(f3,axiom,(
% 1.37/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.57  fof(f139,plain,(
% 1.37/0.57    r1_tarski(sK2,sK4) | ~spl12_11),
% 1.37/0.57    inference(avatar_component_clause,[],[f138])).
% 1.37/0.57  fof(f490,plain,(
% 1.37/0.57    spl12_12 | ~spl12_29),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f483])).
% 1.37/0.57  fof(f483,plain,(
% 1.37/0.57    $false | (spl12_12 | ~spl12_29)),
% 1.37/0.57    inference(resolution,[],[f476,f144])).
% 1.37/0.57  fof(f144,plain,(
% 1.37/0.57    ~r1_tarski(sK4,sK2) | spl12_12),
% 1.37/0.57    inference(avatar_component_clause,[],[f142])).
% 1.37/0.57  fof(f476,plain,(
% 1.37/0.57    r1_tarski(sK4,sK2) | (spl12_12 | ~spl12_29)),
% 1.37/0.57    inference(resolution,[],[f472,f154])).
% 1.37/0.57  fof(f154,plain,(
% 1.37/0.57    r2_hidden(sK6(sK4,sK2),sK4) | spl12_12),
% 1.37/0.57    inference(resolution,[],[f144,f51])).
% 1.37/0.57  fof(f472,plain,(
% 1.37/0.57    ( ! [X3] : (~r2_hidden(sK6(X3,sK2),sK4) | r1_tarski(X3,sK2)) ) | ~spl12_29),
% 1.37/0.57    inference(resolution,[],[f441,f52])).
% 1.37/0.57  fof(f441,plain,(
% 1.37/0.57    ( ! [X4] : (r2_hidden(X4,sK2) | ~r2_hidden(X4,sK4)) ) | ~spl12_29),
% 1.37/0.57    inference(avatar_component_clause,[],[f440])).
% 1.37/0.57  fof(f440,plain,(
% 1.37/0.57    spl12_29 <=> ! [X4] : (~r2_hidden(X4,sK4) | r2_hidden(X4,sK2))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 1.37/0.57  fof(f468,plain,(
% 1.37/0.57    spl12_6 | ~spl12_9 | ~spl12_28),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f463])).
% 1.37/0.57  fof(f463,plain,(
% 1.37/0.57    $false | (spl12_6 | ~spl12_9 | ~spl12_28)),
% 1.37/0.57    inference(resolution,[],[f438,f394])).
% 1.37/0.57  fof(f394,plain,(
% 1.37/0.57    r2_hidden(sK6(sK1,k1_xboole_0),sK3) | (spl12_6 | ~spl12_9)),
% 1.37/0.57    inference(resolution,[],[f129,f159])).
% 1.37/0.57  fof(f159,plain,(
% 1.37/0.57    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK6(sK1,k1_xboole_0),X0)) ) | spl12_6),
% 1.37/0.57    inference(resolution,[],[f148,f50])).
% 1.37/0.57  fof(f50,plain,(
% 1.37/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f27])).
% 1.37/0.57  fof(f148,plain,(
% 1.37/0.57    r2_hidden(sK6(sK1,k1_xboole_0),sK1) | spl12_6),
% 1.37/0.57    inference(resolution,[],[f114,f51])).
% 1.37/0.57  fof(f114,plain,(
% 1.37/0.57    ~r1_tarski(sK1,k1_xboole_0) | spl12_6),
% 1.37/0.57    inference(avatar_component_clause,[],[f112])).
% 1.37/0.57  fof(f112,plain,(
% 1.37/0.57    spl12_6 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.37/0.57  fof(f129,plain,(
% 1.37/0.57    r1_tarski(sK1,sK3) | ~spl12_9),
% 1.37/0.57    inference(avatar_component_clause,[],[f128])).
% 1.37/0.57  fof(f128,plain,(
% 1.37/0.57    spl12_9 <=> r1_tarski(sK1,sK3)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.37/0.57  fof(f438,plain,(
% 1.37/0.57    ( ! [X5] : (~r2_hidden(X5,sK3)) ) | ~spl12_28),
% 1.37/0.57    inference(avatar_component_clause,[],[f437])).
% 1.37/0.57  fof(f437,plain,(
% 1.37/0.57    spl12_28 <=> ! [X5] : ~r2_hidden(X5,sK3)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 1.37/0.57  fof(f449,plain,(
% 1.37/0.57    spl12_30 | spl12_31),
% 1.37/0.57    inference(avatar_split_clause,[],[f434,f447,f444])).
% 1.37/0.57  fof(f434,plain,(
% 1.37/0.57    ( ! [X6,X7] : (~r2_hidden(X6,sK4) | ~r2_hidden(X7,sK3) | r2_hidden(X7,sK1)) )),
% 1.37/0.57    inference(resolution,[],[f315,f66])).
% 1.37/0.57  fof(f66,plain,(
% 1.37/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f38])).
% 1.37/0.57  fof(f38,plain,(
% 1.37/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.37/0.57    inference(flattening,[],[f37])).
% 1.37/0.57  fof(f37,plain,(
% 1.37/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.37/0.57    inference(nnf_transformation,[],[f7])).
% 1.37/0.57  fof(f7,axiom,(
% 1.37/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.37/0.57  fof(f315,plain,(
% 1.37/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,sK3)) )),
% 1.37/0.57    inference(superposition,[],[f68,f39])).
% 1.37/0.57  fof(f39,plain,(
% 1.37/0.57    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.37/0.57    inference(cnf_transformation,[],[f19])).
% 1.37/0.57  fof(f19,plain,(
% 1.37/0.57    (sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.37/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f18])).
% 1.37/0.57  fof(f18,plain,(
% 1.37/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4))),
% 1.37/0.57    introduced(choice_axiom,[])).
% 1.37/0.57  fof(f13,plain,(
% 1.37/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.37/0.57    inference(flattening,[],[f12])).
% 1.37/0.57  fof(f12,plain,(
% 1.37/0.57    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.37/0.57    inference(ennf_transformation,[],[f10])).
% 1.37/0.57  fof(f10,negated_conjecture,(
% 1.37/0.57    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.57    inference(negated_conjecture,[],[f9])).
% 1.37/0.57  fof(f9,conjecture,(
% 1.37/0.57    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.37/0.57  fof(f68,plain,(
% 1.37/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f38])).
% 1.37/0.57  fof(f442,plain,(
% 1.37/0.57    spl12_28 | spl12_29),
% 1.37/0.57    inference(avatar_split_clause,[],[f433,f440,f437])).
% 1.37/0.57  fof(f433,plain,(
% 1.37/0.57    ( ! [X4,X5] : (~r2_hidden(X4,sK4) | ~r2_hidden(X5,sK3) | r2_hidden(X4,sK2)) )),
% 1.37/0.57    inference(resolution,[],[f315,f67])).
% 1.37/0.57  fof(f67,plain,(
% 1.37/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f38])).
% 1.37/0.57  fof(f392,plain,(
% 1.37/0.57    spl12_8 | ~spl12_25),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f389])).
% 1.37/0.57  fof(f389,plain,(
% 1.37/0.57    $false | (spl12_8 | ~spl12_25)),
% 1.37/0.57    inference(resolution,[],[f330,f150])).
% 1.37/0.57  fof(f330,plain,(
% 1.37/0.57    ( ! [X10] : (~r2_hidden(X10,sK2)) ) | ~spl12_25),
% 1.37/0.57    inference(avatar_component_clause,[],[f329])).
% 1.37/0.57  fof(f329,plain,(
% 1.37/0.57    spl12_25 <=> ! [X10] : ~r2_hidden(X10,sK2)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 1.37/0.57  fof(f386,plain,(
% 1.37/0.57    spl12_9 | ~spl12_24),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f380])).
% 1.37/0.57  fof(f380,plain,(
% 1.37/0.57    $false | (spl12_9 | ~spl12_24)),
% 1.37/0.57    inference(resolution,[],[f376,f130])).
% 1.37/0.57  fof(f130,plain,(
% 1.37/0.57    ~r1_tarski(sK1,sK3) | spl12_9),
% 1.37/0.57    inference(avatar_component_clause,[],[f128])).
% 1.37/0.57  fof(f376,plain,(
% 1.37/0.57    r1_tarski(sK1,sK3) | (spl12_9 | ~spl12_24)),
% 1.37/0.57    inference(resolution,[],[f344,f151])).
% 1.37/0.57  fof(f151,plain,(
% 1.37/0.57    r2_hidden(sK6(sK1,sK3),sK1) | spl12_9),
% 1.37/0.57    inference(resolution,[],[f130,f51])).
% 1.37/0.57  fof(f344,plain,(
% 1.37/0.57    ( ! [X2] : (~r2_hidden(sK6(X2,sK3),sK1) | r1_tarski(X2,sK3)) ) | ~spl12_24),
% 1.37/0.57    inference(resolution,[],[f327,f52])).
% 1.37/0.57  fof(f327,plain,(
% 1.37/0.57    ( ! [X11] : (r2_hidden(X11,sK3) | ~r2_hidden(X11,sK1)) ) | ~spl12_24),
% 1.37/0.57    inference(avatar_component_clause,[],[f326])).
% 1.37/0.57  fof(f326,plain,(
% 1.37/0.57    spl12_24 <=> ! [X11] : (~r2_hidden(X11,sK1) | r2_hidden(X11,sK3))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 1.37/0.57  fof(f355,plain,(
% 1.37/0.57    spl12_11 | ~spl12_23),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f349])).
% 1.37/0.57  fof(f349,plain,(
% 1.37/0.57    $false | (spl12_11 | ~spl12_23)),
% 1.37/0.57    inference(resolution,[],[f345,f140])).
% 1.37/0.57  fof(f140,plain,(
% 1.37/0.57    ~r1_tarski(sK2,sK4) | spl12_11),
% 1.37/0.57    inference(avatar_component_clause,[],[f138])).
% 1.37/0.57  fof(f345,plain,(
% 1.37/0.57    r1_tarski(sK2,sK4) | (spl12_11 | ~spl12_23)),
% 1.37/0.57    inference(resolution,[],[f342,f153])).
% 1.37/0.57  fof(f153,plain,(
% 1.37/0.57    r2_hidden(sK6(sK2,sK4),sK2) | spl12_11),
% 1.37/0.57    inference(resolution,[],[f140,f51])).
% 1.37/0.57  fof(f342,plain,(
% 1.37/0.57    ( ! [X2] : (~r2_hidden(sK6(X2,sK4),sK2) | r1_tarski(X2,sK4)) ) | ~spl12_23),
% 1.37/0.57    inference(resolution,[],[f323,f52])).
% 1.37/0.57  fof(f323,plain,(
% 1.37/0.57    ( ! [X8] : (r2_hidden(X8,sK4) | ~r2_hidden(X8,sK2)) ) | ~spl12_23),
% 1.37/0.57    inference(avatar_component_clause,[],[f322])).
% 1.37/0.57  fof(f322,plain,(
% 1.37/0.57    spl12_23 <=> ! [X8] : (~r2_hidden(X8,sK2) | r2_hidden(X8,sK4))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 1.37/0.57  fof(f340,plain,(
% 1.37/0.57    spl12_6 | ~spl12_22),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f335])).
% 1.37/0.57  fof(f335,plain,(
% 1.37/0.57    $false | (spl12_6 | ~spl12_22)),
% 1.37/0.57    inference(resolution,[],[f320,f148])).
% 1.37/0.57  fof(f320,plain,(
% 1.37/0.57    ( ! [X9] : (~r2_hidden(X9,sK1)) ) | ~spl12_22),
% 1.37/0.57    inference(avatar_component_clause,[],[f319])).
% 1.37/0.57  fof(f319,plain,(
% 1.37/0.57    spl12_22 <=> ! [X9] : ~r2_hidden(X9,sK1)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 1.37/0.57  fof(f331,plain,(
% 1.37/0.57    spl12_24 | spl12_25),
% 1.37/0.57    inference(avatar_split_clause,[],[f313,f329,f326])).
% 1.37/0.57  fof(f313,plain,(
% 1.37/0.57    ( ! [X10,X11] : (~r2_hidden(X10,sK2) | ~r2_hidden(X11,sK1) | r2_hidden(X11,sK3)) )),
% 1.37/0.57    inference(resolution,[],[f68,f189])).
% 1.37/0.57  fof(f189,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | r2_hidden(X0,sK3)) )),
% 1.37/0.57    inference(superposition,[],[f66,f39])).
% 1.37/0.57  fof(f324,plain,(
% 1.37/0.57    spl12_22 | spl12_23),
% 1.37/0.57    inference(avatar_split_clause,[],[f312,f322,f319])).
% 1.37/0.57  fof(f312,plain,(
% 1.37/0.57    ( ! [X8,X9] : (~r2_hidden(X8,sK2) | ~r2_hidden(X9,sK1) | r2_hidden(X8,sK4)) )),
% 1.37/0.57    inference(resolution,[],[f68,f204])).
% 1.37/0.57  fof(f204,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | r2_hidden(X1,sK4)) )),
% 1.37/0.57    inference(superposition,[],[f67,f39])).
% 1.37/0.57  fof(f162,plain,(
% 1.37/0.57    ~spl12_4 | spl12_7),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f160])).
% 1.37/0.57  fof(f160,plain,(
% 1.37/0.57    $false | (~spl12_4 | spl12_7)),
% 1.37/0.57    inference(resolution,[],[f149,f93])).
% 1.37/0.57  fof(f93,plain,(
% 1.37/0.57    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl12_4),
% 1.37/0.57    inference(avatar_component_clause,[],[f92])).
% 1.37/0.57  fof(f92,plain,(
% 1.37/0.57    spl12_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.37/0.57  fof(f149,plain,(
% 1.37/0.57    r2_hidden(sK6(k1_xboole_0,sK2),k1_xboole_0) | spl12_7),
% 1.37/0.57    inference(resolution,[],[f120,f51])).
% 1.37/0.57  fof(f120,plain,(
% 1.37/0.57    ~r1_tarski(k1_xboole_0,sK2) | spl12_7),
% 1.37/0.57    inference(avatar_component_clause,[],[f118])).
% 1.37/0.57  fof(f118,plain,(
% 1.37/0.57    spl12_7 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.37/0.57  fof(f157,plain,(
% 1.37/0.57    ~spl12_4 | spl12_5),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f155])).
% 1.37/0.57  fof(f155,plain,(
% 1.37/0.57    $false | (~spl12_4 | spl12_5)),
% 1.37/0.57    inference(resolution,[],[f147,f93])).
% 1.37/0.57  fof(f147,plain,(
% 1.37/0.57    r2_hidden(sK6(k1_xboole_0,sK1),k1_xboole_0) | spl12_5),
% 1.37/0.57    inference(resolution,[],[f110,f51])).
% 1.37/0.57  fof(f110,plain,(
% 1.37/0.57    ~r1_tarski(k1_xboole_0,sK1) | spl12_5),
% 1.37/0.57    inference(avatar_component_clause,[],[f108])).
% 1.37/0.57  fof(f108,plain,(
% 1.37/0.57    spl12_5 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.37/0.57  fof(f136,plain,(
% 1.37/0.57    ~spl12_10 | ~spl12_9 | spl12_1),
% 1.37/0.57    inference(avatar_split_clause,[],[f102,f76,f128,f132])).
% 1.37/0.57  fof(f76,plain,(
% 1.37/0.57    spl12_1 <=> sK1 = sK3),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.37/0.57  fof(f102,plain,(
% 1.37/0.57    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK3,sK1) | spl12_1),
% 1.37/0.57    inference(extensionality_resolution,[],[f49,f78])).
% 1.37/0.57  fof(f78,plain,(
% 1.37/0.57    sK1 != sK3 | spl12_1),
% 1.37/0.57    inference(avatar_component_clause,[],[f76])).
% 1.37/0.57  fof(f126,plain,(
% 1.37/0.57    ~spl12_8 | ~spl12_7),
% 1.37/0.57    inference(avatar_split_clause,[],[f100,f118,f122])).
% 1.37/0.57  fof(f100,plain,(
% 1.37/0.57    ~r1_tarski(k1_xboole_0,sK2) | ~r1_tarski(sK2,k1_xboole_0)),
% 1.37/0.57    inference(extensionality_resolution,[],[f49,f41])).
% 1.37/0.57  fof(f41,plain,(
% 1.37/0.57    k1_xboole_0 != sK2),
% 1.37/0.57    inference(cnf_transformation,[],[f19])).
% 1.37/0.57  fof(f116,plain,(
% 1.37/0.57    ~spl12_6 | ~spl12_5),
% 1.37/0.57    inference(avatar_split_clause,[],[f98,f108,f112])).
% 1.37/0.57  fof(f98,plain,(
% 1.37/0.57    ~r1_tarski(k1_xboole_0,sK1) | ~r1_tarski(sK1,k1_xboole_0)),
% 1.37/0.57    inference(extensionality_resolution,[],[f49,f40])).
% 1.37/0.57  fof(f40,plain,(
% 1.37/0.57    k1_xboole_0 != sK1),
% 1.37/0.57    inference(cnf_transformation,[],[f19])).
% 1.37/0.57  fof(f96,plain,(
% 1.37/0.57    ~spl12_3),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f95])).
% 1.37/0.57  fof(f95,plain,(
% 1.37/0.57    $false | ~spl12_3),
% 1.37/0.57    inference(resolution,[],[f90,f43])).
% 1.37/0.57  fof(f43,plain,(
% 1.37/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f5])).
% 1.37/0.57  fof(f5,axiom,(
% 1.37/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.37/0.57  fof(f90,plain,(
% 1.37/0.57    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl12_3),
% 1.37/0.57    inference(avatar_component_clause,[],[f89])).
% 1.37/0.57  fof(f89,plain,(
% 1.37/0.57    spl12_3 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.37/0.57  fof(f94,plain,(
% 1.37/0.57    spl12_3 | spl12_4),
% 1.37/0.57    inference(avatar_split_clause,[],[f87,f92,f89])).
% 1.37/0.57  fof(f87,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.57    inference(superposition,[],[f46,f44])).
% 1.37/0.57  fof(f44,plain,(
% 1.37/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f4])).
% 1.37/0.57  fof(f4,axiom,(
% 1.37/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.37/0.57  fof(f46,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f21])).
% 1.37/0.57  fof(f21,plain,(
% 1.37/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.37/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f20])).
% 1.37/0.57  fof(f20,plain,(
% 1.37/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.37/0.57    introduced(choice_axiom,[])).
% 1.37/0.57  fof(f14,plain,(
% 1.37/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.37/0.57    inference(ennf_transformation,[],[f11])).
% 1.37/0.57  fof(f11,plain,(
% 1.37/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.57    inference(rectify,[],[f2])).
% 1.37/0.57  fof(f2,axiom,(
% 1.37/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.37/0.57  fof(f83,plain,(
% 1.37/0.57    ~spl12_1 | ~spl12_2),
% 1.37/0.57    inference(avatar_split_clause,[],[f42,f80,f76])).
% 1.37/0.57  fof(f42,plain,(
% 1.37/0.57    sK2 != sK4 | sK1 != sK3),
% 1.37/0.57    inference(cnf_transformation,[],[f19])).
% 1.37/0.57  % SZS output end Proof for theBenchmark
% 1.37/0.57  % (17040)------------------------------
% 1.37/0.57  % (17040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (17040)Termination reason: Refutation
% 1.37/0.57  
% 1.37/0.57  % (17040)Memory used [KB]: 6396
% 1.37/0.57  % (17040)Time elapsed: 0.153 s
% 1.37/0.57  % (17040)------------------------------
% 1.37/0.57  % (17040)------------------------------
% 1.37/0.58  % (17027)Success in time 0.218 s
%------------------------------------------------------------------------------
