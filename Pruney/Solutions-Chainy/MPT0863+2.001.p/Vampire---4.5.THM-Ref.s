%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 174 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 ( 782 expanded)
%              Number of equality atoms :   86 ( 335 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f84,f89,f102,f108,f181,f192,f214,f243,f268,f281])).

fof(f281,plain,
    ( spl7_2
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl7_2
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f278,f72])).

fof(f72,plain,
    ( sK4 != k2_mcart_1(sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_2
  <=> sK4 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f278,plain,
    ( sK4 = k2_mcart_1(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f242,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f242,plain,
    ( r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_12
  <=> r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f268,plain,
    ( spl7_4
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl7_4
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f265,f82])).

fof(f82,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_4
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f265,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl7_11 ),
    inference(resolution,[],[f238,f62])).

fof(f238,plain,
    ( r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_11
  <=> r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f243,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f231,f105,f240,f236])).

fof(f105,plain,
    ( spl7_7
  <=> r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f231,plain,
    ( r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0)))
    | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))
    | ~ spl7_7 ),
    inference(resolution,[],[f162,f61])).

fof(f61,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f162,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k2_mcart_1(sK0),X7)
        | r2_hidden(sK4,X7)
        | r2_hidden(sK3,X7) )
    | ~ spl7_7 ),
    inference(resolution,[],[f121,f107])).

fof(f107,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f121,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X11,k2_tarski(X9,X10))
      | ~ r2_hidden(X11,X8)
      | r2_hidden(X10,X8)
      | r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f58,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f214,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f210,f178,f66])).

% (5450)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f66,plain,
    ( spl7_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f178,plain,
    ( spl7_9
  <=> r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f210,plain,
    ( sK2 = k1_mcart_1(sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f180,f62])).

fof(f180,plain,
    ( r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f192,plain,
    ( spl7_3
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f189,f77])).

fof(f77,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f189,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f176,f62])).

fof(f176,plain,
    ( r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_8
  <=> r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f181,plain,
    ( spl7_8
    | spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f169,f99,f178,f174])).

fof(f99,plain,
    ( spl7_6
  <=> r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f169,plain,
    ( r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0)))
    | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))
    | ~ spl7_6 ),
    inference(resolution,[],[f161,f61])).

fof(f161,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_mcart_1(sK0),X6)
        | r2_hidden(sK2,X6)
        | r2_hidden(sK1,X6) )
    | ~ spl7_6 ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f108,plain,
    ( spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f103,f86,f105])).

% (5452)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f86,plain,
    ( spl7_5
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f103,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))
    | ~ spl7_5 ),
    inference(resolution,[],[f36,f88])).

fof(f88,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f102,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f97,f86,f99])).

fof(f97,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_5 ),
    inference(resolution,[],[f35,f88])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f86])).

fof(f30,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( sK4 != k2_mcart_1(sK0)
          & sK3 != k2_mcart_1(sK0) )
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f84,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f31,f80,f75])).

fof(f31,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f32,f80,f66])).

fof(f32,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,
    ( ~ spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f33,f70,f75])).

fof(f33,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f70,f66])).

fof(f34,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5431)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (5456)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (5440)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (5431)Refutation not found, incomplete strategy% (5431)------------------------------
% 0.20/0.52  % (5431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5431)Memory used [KB]: 1663
% 0.20/0.52  % (5431)Time elapsed: 0.110 s
% 0.20/0.52  % (5431)------------------------------
% 0.20/0.52  % (5431)------------------------------
% 0.20/0.52  % (5456)Refutation not found, incomplete strategy% (5456)------------------------------
% 0.20/0.52  % (5456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5456)Memory used [KB]: 6140
% 0.20/0.52  % (5456)Time elapsed: 0.111 s
% 0.20/0.52  % (5456)------------------------------
% 0.20/0.52  % (5456)------------------------------
% 0.20/0.52  % (5442)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (5442)Refutation not found, incomplete strategy% (5442)------------------------------
% 0.20/0.53  % (5442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5442)Memory used [KB]: 10618
% 0.20/0.53  % (5442)Time elapsed: 0.116 s
% 0.20/0.53  % (5442)------------------------------
% 0.20/0.53  % (5442)------------------------------
% 0.20/0.53  % (5458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (5451)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (5430)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (5432)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (5433)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (5438)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (5458)Refutation not found, incomplete strategy% (5458)------------------------------
% 0.20/0.54  % (5458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5458)Memory used [KB]: 10746
% 0.20/0.54  % (5458)Time elapsed: 0.119 s
% 0.20/0.54  % (5458)------------------------------
% 0.20/0.54  % (5458)------------------------------
% 0.20/0.54  % (5434)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (5439)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (5444)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (5440)Refutation not found, incomplete strategy% (5440)------------------------------
% 0.20/0.54  % (5440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5440)Memory used [KB]: 10746
% 0.20/0.54  % (5440)Time elapsed: 0.136 s
% 0.20/0.54  % (5440)------------------------------
% 0.20/0.54  % (5440)------------------------------
% 0.20/0.54  % (5457)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (5453)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (5457)Refutation not found, incomplete strategy% (5457)------------------------------
% 0.20/0.54  % (5457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5457)Memory used [KB]: 6140
% 0.20/0.54  % (5457)Time elapsed: 0.139 s
% 0.20/0.54  % (5457)------------------------------
% 0.20/0.54  % (5457)------------------------------
% 0.20/0.55  % (5451)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f282,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f73,f78,f83,f84,f89,f102,f108,f181,f192,f214,f243,f268,f281])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    spl7_2 | ~spl7_12),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f280])).
% 0.20/0.55  fof(f280,plain,(
% 0.20/0.55    $false | (spl7_2 | ~spl7_12)),
% 0.20/0.55    inference(subsumption_resolution,[],[f278,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    sK4 != k2_mcart_1(sK0) | spl7_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    spl7_2 <=> sK4 = k2_mcart_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.55  fof(f278,plain,(
% 0.20/0.55    sK4 = k2_mcart_1(sK0) | ~spl7_12),
% 0.20/0.55    inference(resolution,[],[f242,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0))) | ~spl7_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f240])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    spl7_12 <=> r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.55  fof(f268,plain,(
% 0.20/0.55    spl7_4 | ~spl7_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    $false | (spl7_4 | ~spl7_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f265,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    sK3 != k2_mcart_1(sK0) | spl7_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    spl7_4 <=> sK3 = k2_mcart_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    sK3 = k2_mcart_1(sK0) | ~spl7_11),
% 0.20/0.55    inference(resolution,[],[f238,f62])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) | ~spl7_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f236])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    spl7_11 <=> r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    spl7_11 | spl7_12 | ~spl7_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f231,f105,f240,f236])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    spl7_7 <=> r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0))) | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) | ~spl7_7),
% 0.20/0.55    inference(resolution,[],[f162,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.55    inference(equality_resolution,[],[f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.55    inference(equality_resolution,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X7] : (~r2_hidden(k2_mcart_1(sK0),X7) | r2_hidden(sK4,X7) | r2_hidden(sK3,X7)) ) | ~spl7_7),
% 0.20/0.55    inference(resolution,[],[f121,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) | ~spl7_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f105])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    ( ! [X10,X8,X11,X9] : (~r2_hidden(X11,k2_tarski(X9,X10)) | ~r2_hidden(X11,X8) | r2_hidden(X10,X8) | r2_hidden(X9,X8)) )),
% 0.20/0.55    inference(superposition,[],[f58,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(rectify,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.55  fof(f214,plain,(
% 0.20/0.55    spl7_1 | ~spl7_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f210,f178,f66])).
% 0.20/0.55  % (5450)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl7_1 <=> sK2 = k1_mcart_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    spl7_9 <=> r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    sK2 = k1_mcart_1(sK0) | ~spl7_9),
% 0.20/0.55    inference(resolution,[],[f180,f62])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0))) | ~spl7_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f178])).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    spl7_3 | ~spl7_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f191])).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    $false | (spl7_3 | ~spl7_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f189,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    sK1 != k1_mcart_1(sK0) | spl7_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl7_3 <=> sK1 = k1_mcart_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    sK1 = k1_mcart_1(sK0) | ~spl7_8),
% 0.20/0.55    inference(resolution,[],[f176,f62])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) | ~spl7_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    spl7_8 <=> r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    spl7_8 | spl7_9 | ~spl7_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f169,f99,f178,f174])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    spl7_6 <=> r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0))) | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) | ~spl7_6),
% 0.20/0.55    inference(resolution,[],[f161,f61])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),X6) | r2_hidden(sK2,X6) | r2_hidden(sK1,X6)) ) | ~spl7_6),
% 0.20/0.55    inference(resolution,[],[f121,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) | ~spl7_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f99])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    spl7_7 | ~spl7_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f103,f86,f105])).
% 0.20/0.55  % (5452)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    spl7_5 <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) | ~spl7_5),
% 0.20/0.55    inference(resolution,[],[f36,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) | ~spl7_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f86])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    spl7_6 | ~spl7_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f97,f86,f99])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) | ~spl7_5),
% 0.20/0.55    inference(resolution,[],[f35,f88])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    spl7_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f30,f86])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ~spl7_3 | ~spl7_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f31,f80,f75])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ~spl7_1 | ~spl7_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f32,f80,f66])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ~spl7_3 | ~spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f70,f75])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ~spl7_1 | ~spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f70,f66])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (5451)------------------------------
% 0.20/0.55  % (5451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5451)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (5451)Memory used [KB]: 6396
% 0.20/0.55  % (5451)Time elapsed: 0.138 s
% 0.20/0.55  % (5451)------------------------------
% 0.20/0.55  % (5451)------------------------------
% 0.20/0.55  % (5454)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (5429)Success in time 0.187 s
%------------------------------------------------------------------------------
