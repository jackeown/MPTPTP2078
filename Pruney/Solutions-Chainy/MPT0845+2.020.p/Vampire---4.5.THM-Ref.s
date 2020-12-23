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
% DateTime   : Thu Dec  3 12:58:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 134 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 410 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f54,f78,f96,f112,f114,f139,f163,f167,f172,f209,f225])).

fof(f225,plain,
    ( ~ spl6_4
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f72,f207])).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_26
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f72,plain,
    ( r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_4
  <=> r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f209,plain,
    ( spl6_26
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f201,f165,f161,f206])).

fof(f161,plain,
    ( spl6_19
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f165,plain,
    ( spl6_20
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_20 ),
    inference(resolution,[],[f166,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f166,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f172,plain,
    ( ~ spl6_17
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f168,f137,f152])).

fof(f152,plain,
    ( spl6_17
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f137,plain,
    ( spl6_15
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f168,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f138,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f138,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f167,plain,
    ( spl6_20
    | spl6_17 ),
    inference(avatar_split_clause,[],[f159,f152,f165])).

fof(f159,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | spl6_17 ),
    inference(resolution,[],[f153,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f153,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f163,plain,
    ( spl6_19
    | spl6_17 ),
    inference(avatar_split_clause,[],[f158,f152,f161])).

fof(f158,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_17 ),
    inference(resolution,[],[f153,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f139,plain,
    ( spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f130,f71,f137])).

fof(f130,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f111,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f111,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_11
  <=> r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f112,plain,
    ( ~ spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f104,f94,f110])).

% (23229)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f94,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f104,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | ~ spl6_8 ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f95,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f82,f74,f94])).

fof(f74,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f82,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f39])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f78,plain,
    ( spl6_4
    | spl6_5
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f52,f44,f74,f71])).

fof(f44,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f52,plain,
    ( spl6_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0)
    | r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_3 ),
    inference(superposition,[],[f53,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = sK0
      | r2_hidden(k4_tarski(sK2(X0,sK0),sK3(X0,sK0)),X0)
      | r2_hidden(sK1(sK2(X0,sK0),sK0),sK0) ) ),
    inference(resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X13] :
      ( ~ r1_xboole_0(sK2(X13,sK0),sK0)
      | sK0 = k1_relat_1(X13)
      | r2_hidden(k4_tarski(sK2(X13,sK0),sK3(X13,sK0)),X13) ) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f53,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (23232)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (23232)Refutation not found, incomplete strategy% (23232)------------------------------
% 0.20/0.49  % (23232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23232)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23232)Memory used [KB]: 10618
% 0.20/0.49  % (23232)Time elapsed: 0.090 s
% 0.20/0.49  % (23232)------------------------------
% 0.20/0.49  % (23232)------------------------------
% 0.20/0.50  % (23240)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (23240)Refutation not found, incomplete strategy% (23240)------------------------------
% 0.20/0.51  % (23240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23234)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (23240)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23240)Memory used [KB]: 10618
% 0.20/0.51  % (23240)Time elapsed: 0.104 s
% 0.20/0.51  % (23240)------------------------------
% 0.20/0.51  % (23240)------------------------------
% 0.20/0.52  % (23246)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % (23231)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (23242)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (23233)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (23235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.53  % (23248)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  % (23243)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.53  % (23235)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (23236)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f46,f54,f78,f96,f112,f114,f139,f163,f167,f172,f209,f225])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    ~spl6_4 | ~spl6_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    $false | (~spl6_4 | ~spl6_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f72,f207])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f206])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    spl6_26 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) | ~spl6_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl6_4 <=> r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.30/0.53  fof(f209,plain,(
% 1.30/0.53    spl6_26 | ~spl6_19 | ~spl6_20),
% 1.30/0.53    inference(avatar_split_clause,[],[f201,f165,f161,f206])).
% 1.30/0.53  fof(f161,plain,(
% 1.30/0.53    spl6_19 <=> r2_hidden(sK1(sK5(sK0),sK0),sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.30/0.53  fof(f165,plain,(
% 1.30/0.53    spl6_20 <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.30/0.53  fof(f201,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_20),
% 1.30/0.53    inference(resolution,[],[f166,f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 1.30/0.53  fof(f166,plain,(
% 1.30/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | ~spl6_20),
% 1.30/0.53    inference(avatar_component_clause,[],[f165])).
% 1.30/0.53  fof(f172,plain,(
% 1.30/0.53    ~spl6_17 | ~spl6_15),
% 1.30/0.53    inference(avatar_split_clause,[],[f168,f137,f152])).
% 1.30/0.53  fof(f152,plain,(
% 1.30/0.53    spl6_17 <=> r1_xboole_0(sK5(sK0),sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.30/0.53  fof(f137,plain,(
% 1.30/0.53    spl6_15 <=> r2_hidden(sK5(sK0),sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.30/0.53  fof(f168,plain,(
% 1.30/0.53    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_15),
% 1.30/0.53    inference(resolution,[],[f138,f27])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f10,plain,(
% 1.30/0.53    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,negated_conjecture,(
% 1.30/0.53    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.30/0.53    inference(negated_conjecture,[],[f7])).
% 1.30/0.53  fof(f7,conjecture,(
% 1.30/0.53    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 1.30/0.53  fof(f138,plain,(
% 1.30/0.53    r2_hidden(sK5(sK0),sK0) | ~spl6_15),
% 1.30/0.53    inference(avatar_component_clause,[],[f137])).
% 1.30/0.53  fof(f167,plain,(
% 1.30/0.53    spl6_20 | spl6_17),
% 1.30/0.53    inference(avatar_split_clause,[],[f159,f152,f165])).
% 1.30/0.53  fof(f159,plain,(
% 1.30/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | spl6_17),
% 1.30/0.53    inference(resolution,[],[f153,f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f11,plain,(
% 1.30/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,plain,(
% 1.30/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.53    inference(rectify,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.30/0.53  fof(f153,plain,(
% 1.30/0.53    ~r1_xboole_0(sK5(sK0),sK0) | spl6_17),
% 1.30/0.53    inference(avatar_component_clause,[],[f152])).
% 1.30/0.53  fof(f163,plain,(
% 1.30/0.53    spl6_19 | spl6_17),
% 1.30/0.53    inference(avatar_split_clause,[],[f158,f152,f161])).
% 1.30/0.53  fof(f158,plain,(
% 1.30/0.53    r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_17),
% 1.30/0.53    inference(resolution,[],[f153,f32])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  fof(f139,plain,(
% 1.30/0.53    spl6_15 | ~spl6_4),
% 1.30/0.53    inference(avatar_split_clause,[],[f130,f71,f137])).
% 1.30/0.53  fof(f130,plain,(
% 1.30/0.53    r2_hidden(sK5(sK0),sK0) | ~spl6_4),
% 1.30/0.53    inference(resolution,[],[f72,f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f25])).
% 1.30/0.53  fof(f114,plain,(
% 1.30/0.53    spl6_11),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f113])).
% 1.30/0.53  fof(f113,plain,(
% 1.30/0.53    $false | spl6_11),
% 1.30/0.53    inference(resolution,[],[f111,f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.30/0.53  fof(f111,plain,(
% 1.30/0.53    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | spl6_11),
% 1.30/0.53    inference(avatar_component_clause,[],[f110])).
% 1.30/0.53  fof(f110,plain,(
% 1.30/0.53    spl6_11 <=> r1_tarski(k1_xboole_0,sK5(k1_xboole_0))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.30/0.53  fof(f112,plain,(
% 1.30/0.53    ~spl6_11 | ~spl6_8),
% 1.30/0.53    inference(avatar_split_clause,[],[f104,f94,f110])).
% 1.30/0.53  % (23229)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.30/0.53  fof(f94,plain,(
% 1.30/0.53    spl6_8 <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.30/0.53  fof(f104,plain,(
% 1.30/0.53    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | ~spl6_8),
% 1.30/0.53    inference(resolution,[],[f95,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.30/0.53    inference(ennf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.30/0.53  fof(f95,plain,(
% 1.30/0.53    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_8),
% 1.30/0.53    inference(avatar_component_clause,[],[f94])).
% 1.30/0.53  fof(f96,plain,(
% 1.30/0.53    spl6_8 | ~spl6_5),
% 1.30/0.53    inference(avatar_split_clause,[],[f82,f74,f94])).
% 1.30/0.53  fof(f74,plain,(
% 1.30/0.53    spl6_5 <=> r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.30/0.53  fof(f82,plain,(
% 1.30/0.53    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_5),
% 1.30/0.53    inference(resolution,[],[f75,f39])).
% 1.30/0.53  fof(f75,plain,(
% 1.30/0.53    r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0) | ~spl6_5),
% 1.30/0.53    inference(avatar_component_clause,[],[f74])).
% 1.30/0.53  fof(f78,plain,(
% 1.30/0.53    spl6_4 | spl6_5 | spl6_1 | ~spl6_3),
% 1.30/0.53    inference(avatar_split_clause,[],[f68,f52,f44,f74,f71])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    spl6_1 <=> k1_xboole_0 = sK0),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    spl6_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    k1_xboole_0 = sK0 | r2_hidden(k4_tarski(sK2(k1_xboole_0,sK0),sK3(k1_xboole_0,sK0)),k1_xboole_0) | r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) | ~spl6_3),
% 1.30/0.53    inference(superposition,[],[f53,f65])).
% 1.30/0.53  fof(f65,plain,(
% 1.30/0.53    ( ! [X0] : (k1_relat_1(X0) = sK0 | r2_hidden(k4_tarski(sK2(X0,sK0),sK3(X0,sK0)),X0) | r2_hidden(sK1(sK2(X0,sK0),sK0),sK0)) )),
% 1.30/0.53    inference(resolution,[],[f62,f32])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    ( ! [X13] : (~r1_xboole_0(sK2(X13,sK0),sK0) | sK0 = k1_relat_1(X13) | r2_hidden(k4_tarski(sK2(X13,sK0),sK3(X13,sK0)),X13)) )),
% 1.30/0.53    inference(resolution,[],[f36,f27])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 1.30/0.53    inference(cnf_transformation,[],[f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.30/0.53    inference(rectify,[],[f18])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f52])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    spl6_3),
% 1.30/0.53    inference(avatar_split_clause,[],[f28,f52])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.53    inference(cnf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ~spl6_1),
% 1.30/0.53    inference(avatar_split_clause,[],[f26,f44])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    k1_xboole_0 != sK0),
% 1.30/0.53    inference(cnf_transformation,[],[f15])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (23235)------------------------------
% 1.30/0.53  % (23235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (23235)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (23235)Memory used [KB]: 10746
% 1.30/0.53  % (23235)Time elapsed: 0.088 s
% 1.30/0.53  % (23235)------------------------------
% 1.30/0.53  % (23235)------------------------------
% 1.30/0.53  % (23244)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.30/0.54  % (23225)Success in time 0.169 s
%------------------------------------------------------------------------------
