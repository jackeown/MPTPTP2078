%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 112 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  229 ( 351 expanded)
%              Number of equality atoms :   44 (  55 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f96,f102,f106,f117,f125,f138,f143,f163])).

fof(f163,plain,
    ( ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f123])).

fof(f123,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f122])).

% (20502)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f122,plain,
    ( spl6_10
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f116,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_9
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f143,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl6_12 ),
    inference(resolution,[],[f135,f60])).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f135,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_12
  <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f138,plain,
    ( spl6_12
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f131,f94,f53,f49,f134])).

fof(f49,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f53,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f94,plain,
    ( spl6_5
  <=> ! [X8] :
        ( sK0 = k2_relat_1(X8)
        | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f131,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(superposition,[],[f54,f95])).

fof(f95,plain,
    ( ! [X8] :
        ( sK0 = k2_relat_1(X8)
        | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f54,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f125,plain,
    ( spl6_10
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f118,f104,f100,f122])).

fof(f100,plain,
    ( spl6_6
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f104,plain,
    ( spl6_7
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).

fof(f25,plain,(
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

fof(f105,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f117,plain,
    ( spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f109,f100,f115])).

fof(f109,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f101,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f106,plain,
    ( spl6_7
    | spl6_4 ),
    inference(avatar_split_clause,[],[f98,f91,f104])).

fof(f91,plain,
    ( spl6_4
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f98,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | spl6_4 ),
    inference(resolution,[],[f92,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).

fof(f15,plain,(
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

fof(f92,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f102,plain,
    ( spl6_6
    | spl6_4 ),
    inference(avatar_split_clause,[],[f97,f91,f100])).

fof(f97,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_4 ),
    inference(resolution,[],[f92,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f88,f94,f91])).

fof(f88,plain,(
    ! [X8] :
      ( sK0 = k2_relat_1(X8)
      | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8)
      | ~ r1_xboole_0(sK5(sK0),sK0) ) ),
    inference(resolution,[],[f67,f28])).

fof(f28,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
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

fof(f67,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(X7),X7)
      | k2_relat_1(X6) = X7
      | r2_hidden(k4_tarski(sK3(X6,X7),sK2(X6,X7)),X6) ) ),
    inference(resolution,[],[f37,f42])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:42:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (20511)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.45  % (20516)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.45  % (20504)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (20503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (20497)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (20503)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f51,f55,f96,f102,f106,f117,f125,f138,f143,f163])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    ~spl6_9 | ~spl6_10),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.46  fof(f159,plain,(
% 0.20/0.46    $false | (~spl6_9 | ~spl6_10)),
% 0.20/0.46    inference(resolution,[],[f116,f123])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f122])).
% 0.20/0.46  % (20502)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    spl6_10 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    r2_hidden(sK5(sK0),sK0) | ~spl6_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f115])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    spl6_9 <=> r2_hidden(sK5(sK0),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    ~spl6_12),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    $false | ~spl6_12),
% 0.20/0.46    inference(resolution,[],[f135,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(superposition,[],[f31,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.46    inference(flattening,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.46    inference(nnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) | ~spl6_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f134])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    spl6_12 <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    spl6_12 | spl6_1 | ~spl6_2 | ~spl6_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f131,f94,f53,f49,f134])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl6_1 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl6_5 <=> ! [X8] : (sK0 = k2_relat_1(X8) | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0),sK2(k1_xboole_0,sK0)),k1_xboole_0) | (~spl6_2 | ~spl6_5)),
% 0.20/0.46    inference(superposition,[],[f54,f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X8] : (sK0 = k2_relat_1(X8) | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8)) ) | ~spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f94])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    spl6_10 | ~spl6_6 | ~spl6_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f118,f104,f100,f122])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    spl6_6 <=> r2_hidden(sK1(sK5(sK0),sK0),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl6_7 <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_7),
% 0.20/0.46    inference(resolution,[],[f105,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | ~spl6_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f104])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl6_9 | ~spl6_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f109,f100,f115])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    r2_hidden(sK5(sK0),sK0) | ~spl6_6),
% 0.20/0.46    inference(resolution,[],[f101,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~spl6_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f100])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl6_7 | spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f98,f91,f104])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl6_4 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | spl6_4),
% 0.20/0.46    inference(resolution,[],[f92,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~r1_xboole_0(sK5(sK0),sK0) | spl6_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f91])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    spl6_6 | spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f97,f91,f100])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_4),
% 0.20/0.46    inference(resolution,[],[f92,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~spl6_4 | spl6_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f88,f94,f91])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X8] : (sK0 = k2_relat_1(X8) | r2_hidden(k4_tarski(sK3(X8,sK0),sK2(X8,sK0)),X8) | ~r1_xboole_0(sK5(sK0),sK0)) )),
% 0.20/0.46    inference(resolution,[],[f67,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X6,X7] : (r2_hidden(sK5(X7),X7) | k2_relat_1(X6) = X7 | r2_hidden(k4_tarski(sK3(X6,X7),sK2(X6,X7)),X6)) )),
% 0.20/0.46    inference(resolution,[],[f37,f42])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.47    inference(rectify,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f53])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ~spl6_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f49])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (20503)------------------------------
% 0.20/0.47  % (20503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20503)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (20503)Memory used [KB]: 10746
% 0.20/0.47  % (20503)Time elapsed: 0.011 s
% 0.20/0.47  % (20503)------------------------------
% 0.20/0.47  % (20503)------------------------------
% 0.20/0.47  % (20508)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (20496)Success in time 0.116 s
%------------------------------------------------------------------------------
