%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 129 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  224 ( 400 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f78,f96,f116,f128,f148,f152,f157,f188,f202])).

fof(f202,plain,
    ( ~ spl6_4
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f72,f186])).

fof(f186,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_20
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f72,plain,
    ( r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_4
  <=> r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f188,plain,
    ( spl6_20
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f180,f150,f146,f185])).

fof(f146,plain,
    ( spl6_15
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f150,plain,
    ( spl6_16
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f151,f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).

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

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f151,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,
    ( ~ spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f153,f126,f137])).

fof(f137,plain,
    ( spl6_13
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f126,plain,
    ( spl6_12
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f153,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f127,f27])).

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

fof(f127,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f152,plain,
    ( spl6_16
    | spl6_13 ),
    inference(avatar_split_clause,[],[f144,f137,f150])).

fof(f144,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | spl6_13 ),
    inference(resolution,[],[f138,f31])).

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

fof(f138,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f148,plain,
    ( spl6_15
    | spl6_13 ),
    inference(avatar_split_clause,[],[f143,f137,f146])).

fof(f143,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_13 ),
    inference(resolution,[],[f138,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f128,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f120,f71,f126])).

fof(f120,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl6_8 ),
    inference(resolution,[],[f99,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f99,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_tarski(sK5(k1_xboole_0),X1),k1_xboole_0)
    | ~ spl6_8 ),
    inference(resolution,[],[f95,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f95,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f96,plain,
    ( spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f83,f74,f94])).

fof(f74,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f83,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f78,plain,
    ( spl6_4
    | spl6_5
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f68,f48,f44,f74,f71])).

fof(f44,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f48,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)
    | r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_2 ),
    inference(superposition,[],[f49,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = sK0
      | r2_hidden(k4_tarski(sK3(X0,sK0),sK2(X0,sK0)),X0)
      | r2_hidden(sK1(sK2(X0,sK0),sK0),sK0) ) ),
    inference(resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X14] :
      ( ~ r1_xboole_0(sK2(X14,sK0),sK0)
      | sK0 = k2_relat_1(X14)
      | r2_hidden(k4_tarski(sK3(X14,sK0),sK2(X14,sK0)),X14) ) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f49,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f29,f48])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (19331)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (19324)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (19319)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (19331)Refutation not found, incomplete strategy% (19331)------------------------------
% 0.20/0.47  % (19331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19331)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19331)Memory used [KB]: 10618
% 0.20/0.47  % (19331)Time elapsed: 0.066 s
% 0.20/0.47  % (19331)------------------------------
% 0.20/0.47  % (19331)------------------------------
% 0.20/0.47  % (19315)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (19312)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (19312)Refutation not found, incomplete strategy% (19312)------------------------------
% 0.20/0.48  % (19312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19312)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (19312)Memory used [KB]: 10618
% 0.20/0.48  % (19312)Time elapsed: 0.069 s
% 0.20/0.48  % (19312)------------------------------
% 0.20/0.48  % (19312)------------------------------
% 0.20/0.48  % (19329)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (19316)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (19318)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (19317)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (19317)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f46,f50,f78,f96,f116,f128,f148,f152,f157,f188,f202])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ~spl6_4 | ~spl6_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    $false | (~spl6_4 | ~spl6_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f72,f186])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl6_20 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) | ~spl6_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl6_4 <=> r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl6_20 | ~spl6_15 | ~spl6_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f180,f150,f146,f185])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl6_15 <=> r2_hidden(sK1(sK5(sK0),sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl6_16 <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_16),
% 0.20/0.49    inference(resolution,[],[f151,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | ~spl6_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f150])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ~spl6_13 | ~spl6_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f153,f126,f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl6_13 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl6_12 <=> r2_hidden(sK5(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_12),
% 0.20/0.49    inference(resolution,[],[f127,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r2_hidden(sK5(sK0),sK0) | ~spl6_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f126])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl6_16 | spl6_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f137,f150])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | spl6_13),
% 0.20/0.49    inference(resolution,[],[f138,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ~r1_xboole_0(sK5(sK0),sK0) | spl6_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl6_15 | spl6_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f143,f137,f146])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_13),
% 0.20/0.49    inference(resolution,[],[f138,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl6_12 | ~spl6_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f120,f71,f126])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    r2_hidden(sK5(sK0),sK0) | ~spl6_4),
% 0.20/0.49    inference(resolution,[],[f72,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ~spl6_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    $false | ~spl6_8),
% 0.20/0.49    inference(resolution,[],[f99,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_xboole_0(k2_tarski(sK5(k1_xboole_0),X1),k1_xboole_0)) ) | ~spl6_8),
% 0.20/0.49    inference(resolution,[],[f95,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl6_8 <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl6_8 | ~spl6_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f83,f74,f94])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl6_5 <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_5),
% 0.20/0.49    inference(resolution,[],[f75,f38])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) | ~spl6_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl6_4 | spl6_5 | spl6_1 | ~spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f48,f44,f74,f71])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl6_1 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) | r2_hidden(sK1(sK2(k1_xboole_0,sK0),sK0),sK0) | ~spl6_2),
% 0.20/0.49    inference(superposition,[],[f49,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(X0) = sK0 | r2_hidden(k4_tarski(sK3(X0,sK0),sK2(X0,sK0)),X0) | r2_hidden(sK1(sK2(X0,sK0),sK0),sK0)) )),
% 0.20/0.49    inference(resolution,[],[f62,f32])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X14] : (~r1_xboole_0(sK2(X14,sK0),sK0) | sK0 = k2_relat_1(X14) | r2_hidden(k4_tarski(sK3(X14,sK0),sK2(X14,sK0)),X14)) )),
% 0.20/0.49    inference(resolution,[],[f36,f27])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.49    inference(rectify,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f48])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~spl6_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f44])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    k1_xboole_0 != sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19317)------------------------------
% 0.20/0.49  % (19317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19317)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19317)Memory used [KB]: 10746
% 0.20/0.49  % (19317)Time elapsed: 0.048 s
% 0.20/0.49  % (19317)------------------------------
% 0.20/0.49  % (19317)------------------------------
% 0.20/0.49  % (19328)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (19310)Success in time 0.139 s
%------------------------------------------------------------------------------
