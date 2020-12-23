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
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 609 expanded)
%              Number of leaves         :   30 ( 190 expanded)
%              Depth                    :   11
%              Number of atoms          :  379 (1683 expanded)
%              Number of equality atoms :   25 ( 365 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f74,f126,f132,f136,f146,f154,f171,f180,f202,f207,f216,f224,f235,f242,f251,f264,f269,f277,f281,f293,f296,f298,f306])).

fof(f306,plain,(
    ~ spl14_13 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl14_13 ),
    inference(unit_resulting_resolution,[],[f44,f44,f176,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X2))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,k1_tarski(X2))
      | ~ r2_hidden(X0,X3) ) ),
    inference(condensation,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k1_tarski(X2))
      | ~ r2_hidden(X0,X5) ) ),
    inference(superposition,[],[f82,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k4_tarski(X0,X2)) = X3
      | ~ r2_hidden(X2,k1_tarski(X3))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_mcart_1(k4_tarski(X2,X0)),X1)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f176,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),X1)
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl14_13
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

% (24696)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (24688)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f44,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f298,plain,
    ( spl14_3
    | ~ spl14_14 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl14_3
    | ~ spl14_14 ),
    inference(unit_resulting_resolution,[],[f44,f61,f179])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k1_tarski(X0))
        | r2_hidden(X0,sK6) )
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl14_14
  <=> ! [X0] :
        ( r2_hidden(X0,sK6)
        | ~ r2_hidden(sK2,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f61,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl14_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl14_3
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f296,plain,
    ( spl14_2
    | ~ spl14_9 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl14_2
    | ~ spl14_9 ),
    inference(unit_resulting_resolution,[],[f44,f56,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k1_tarski(X0))
        | r2_hidden(X0,sK7) )
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl14_9
  <=> ! [X0] :
        ( r2_hidden(X0,sK7)
        | ~ r2_hidden(sK3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f56,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl14_2
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f293,plain,(
    ~ spl14_20 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f44,f44,f231,f97])).

fof(f231,plain,
    ( ! [X1] : ~ r2_hidden(sK0,X1)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl14_20
  <=> ! [X1] : ~ r2_hidden(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f281,plain,
    ( spl14_4
    | ~ spl14_21 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl14_4
    | ~ spl14_21 ),
    inference(unit_resulting_resolution,[],[f44,f66,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tarski(X0))
        | r2_hidden(X0,sK5) )
    | ~ spl14_21 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl14_21
  <=> ! [X0] :
        ( r2_hidden(X0,sK5)
        | ~ r2_hidden(sK1,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl14_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl14_4
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f277,plain,(
    ~ spl14_10 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl14_10 ),
    inference(unit_resulting_resolution,[],[f44,f44,f162,f97])).

fof(f162,plain,
    ( ! [X1] : ~ r2_hidden(sK3,X1)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl14_10
  <=> ! [X1] : ~ r2_hidden(sK3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f269,plain,
    ( spl14_5
    | ~ spl14_24 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl14_5
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f71,f44,f250])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_tarski(X0))
        | r2_hidden(X0,sK4) )
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl14_24
  <=> ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ r2_hidden(sK0,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl14_5
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f264,plain,(
    ~ spl14_23 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl14_23 ),
    inference(unit_resulting_resolution,[],[f44,f44,f247,f97])).

fof(f247,plain,
    ( ! [X1] : ~ r2_hidden(sK1,X1)
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl14_23
  <=> ! [X1] : ~ r2_hidden(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f251,plain,
    ( spl14_23
    | spl14_24
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f244,f240,f249,f246])).

fof(f240,plain,
    ( spl14_22
  <=> ! [X0] :
        ( r2_hidden(k1_mcart_1(X0),sK4)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK4)
        | ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(sK0,k1_tarski(X0)) )
    | ~ spl14_22 ),
    inference(superposition,[],[f243,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X2)) = X1
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k1_mcart_1(k4_tarski(X6,X4)),X7)
      | ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f243,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK4)
    | ~ spl14_22 ),
    inference(resolution,[],[f241,f44])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0))
        | r2_hidden(k1_mcart_1(X0),sK4) )
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( spl14_18
    | spl14_22
    | ~ spl14_17 ),
    inference(avatar_split_clause,[],[f238,f205,f240,f211])).

fof(f211,plain,
    ( spl14_18
  <=> ! [X1] : ~ r2_hidden(sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f205,plain,
    ( spl14_17
  <=> ! [X0] :
        ( r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_mcart_1(X0),sK4)
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) )
    | ~ spl14_17 ),
    inference(superposition,[],[f237,f87])).

fof(f237,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),sK4)
    | ~ spl14_17 ),
    inference(resolution,[],[f206,f44])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))
        | r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4) )
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f205])).

fof(f235,plain,
    ( spl14_20
    | spl14_21
    | ~ spl14_19 ),
    inference(avatar_split_clause,[],[f228,f214,f233,f230])).

fof(f214,plain,
    ( spl14_19
  <=> ! [X0] :
        ( r2_hidden(k2_mcart_1(X0),sK5)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK5)
        | ~ r2_hidden(sK1,k1_tarski(X0))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl14_19 ),
    inference(superposition,[],[f227,f84])).

fof(f227,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK5)
    | ~ spl14_19 ),
    inference(resolution,[],[f215,f44])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0))
        | r2_hidden(k2_mcart_1(X0),sK5) )
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f214])).

fof(f224,plain,(
    ~ spl14_18 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl14_18 ),
    inference(unit_resulting_resolution,[],[f44,f44,f212,f97])).

fof(f212,plain,
    ( ! [X1] : ~ r2_hidden(sK2,X1)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f216,plain,
    ( spl14_18
    | spl14_19
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f209,f200,f214,f211])).

fof(f200,plain,
    ( spl14_16
  <=> ! [X0] :
        ( r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_mcart_1(X0),sK5)
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) )
    | ~ spl14_16 ),
    inference(superposition,[],[f208,f87])).

fof(f208,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),sK5)
    | ~ spl14_16 ),
    inference(resolution,[],[f201,f44])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))
        | r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5) )
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f207,plain,
    ( spl14_10
    | spl14_17
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f203,f51,f205,f161])).

fof(f51,plain,
    ( spl14_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4)
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) )
    | ~ spl14_1 ),
    inference(superposition,[],[f192,f87])).

fof(f192,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)))),sK4)
    | ~ spl14_1 ),
    inference(resolution,[],[f158,f23])).

fof(f158,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),k2_zfmisc_1(sK4,sK5))
    | ~ spl14_1 ),
    inference(resolution,[],[f138,f23])).

fof(f138,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl14_1 ),
    inference(resolution,[],[f53,f23])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f202,plain,
    ( spl14_10
    | spl14_16
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f198,f51,f200,f161])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5)
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) )
    | ~ spl14_1 ),
    inference(superposition,[],[f191,f87])).

fof(f191,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)))),sK5)
    | ~ spl14_1 ),
    inference(resolution,[],[f158,f24])).

fof(f180,plain,
    ( spl14_13
    | spl14_14
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f173,f169,f178,f175])).

fof(f169,plain,
    ( spl14_12
  <=> ! [X0] :
        ( r2_hidden(k2_mcart_1(X0),sK6)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK6)
        | ~ r2_hidden(sK2,k1_tarski(X0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),X1) )
    | ~ spl14_12 ),
    inference(superposition,[],[f172,f84])).

fof(f172,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK6)
    | ~ spl14_12 ),
    inference(resolution,[],[f170,f44])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))
        | r2_hidden(k2_mcart_1(X0),sK6) )
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl14_10
    | spl14_12
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f167,f51,f169,f161])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_mcart_1(X0),sK6)
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) )
    | ~ spl14_1 ),
    inference(superposition,[],[f157,f87])).

fof(f157,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),sK6)
    | ~ spl14_1 ),
    inference(resolution,[],[f138,f24])).

fof(f154,plain,(
    ~ spl14_8 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl14_8 ),
    inference(unit_resulting_resolution,[],[f44,f44,f142,f97])).

fof(f142,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl14_8
  <=> ! [X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f146,plain,
    ( spl14_8
    | spl14_9
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f139,f51,f144,f141])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK7)
        | ~ r2_hidden(sK3,k1_tarski(X0))
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1) )
    | ~ spl14_1 ),
    inference(superposition,[],[f137,f84])).

fof(f137,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),sK7)
    | ~ spl14_1 ),
    inference(resolution,[],[f53,f24])).

fof(f136,plain,
    ( ~ spl14_5
    | ~ spl14_4
    | spl14_7 ),
    inference(avatar_split_clause,[],[f134,f129,f65,f70])).

fof(f129,plain,
    ( spl14_7
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f134,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | spl14_7 ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl14_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( ~ spl14_7
    | ~ spl14_3
    | spl14_6 ),
    inference(avatar_split_clause,[],[f127,f123,f60,f129])).

fof(f123,plain,
    ( spl14_6
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f127,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl14_6 ),
    inference(resolution,[],[f125,f46])).

fof(f125,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl14_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( ~ spl14_6
    | ~ spl14_2
    | spl14_1 ),
    inference(avatar_split_clause,[],[f121,f51,f55,f123])).

fof(f121,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl14_1 ),
    inference(resolution,[],[f52,f46])).

fof(f52,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl14_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f74,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f41,f70,f65,f60,f55,f51])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f12,f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f34,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f33,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f12,plain,
    ( ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f73,plain,
    ( spl14_1
    | spl14_5 ),
    inference(avatar_split_clause,[],[f40,f70,f51])).

fof(f40,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f13,f35,f36])).

fof(f13,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,
    ( spl14_1
    | spl14_4 ),
    inference(avatar_split_clause,[],[f39,f65,f51])).

fof(f39,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f14,f35,f36])).

fof(f14,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,
    ( spl14_1
    | spl14_3 ),
    inference(avatar_split_clause,[],[f38,f60,f51])).

fof(f38,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f15,f35,f36])).

fof(f15,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f37,f55,f51])).

fof(f37,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f16,f35,f36])).

fof(f16,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24691)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (24699)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (24683)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (24699)Refutation not found, incomplete strategy% (24699)------------------------------
% 0.21/0.51  % (24699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24679)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (24680)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (24699)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24699)Memory used [KB]: 10746
% 0.21/0.51  % (24699)Time elapsed: 0.059 s
% 0.21/0.51  % (24699)------------------------------
% 0.21/0.51  % (24699)------------------------------
% 0.21/0.52  % (24687)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.53  % (24703)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.53  % (24681)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.53  % (24682)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (24676)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  % (24702)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (24678)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.54  % (24700)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.54  % (24695)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.54  % (24700)Refutation not found, incomplete strategy% (24700)------------------------------
% 1.40/0.54  % (24700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (24700)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (24700)Memory used [KB]: 10618
% 1.40/0.54  % (24700)Time elapsed: 0.131 s
% 1.40/0.54  % (24700)------------------------------
% 1.40/0.54  % (24700)------------------------------
% 1.40/0.54  % (24705)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.55  % (24693)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (24705)Refutation not found, incomplete strategy% (24705)------------------------------
% 1.40/0.55  % (24705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24705)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24705)Memory used [KB]: 1663
% 1.40/0.55  % (24705)Time elapsed: 0.140 s
% 1.40/0.55  % (24705)------------------------------
% 1.40/0.55  % (24705)------------------------------
% 1.40/0.55  % (24677)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.40/0.55  % (24698)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.55  % (24694)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.55  % (24697)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.55  % (24690)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.55  % (24701)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (24690)Refutation not found, incomplete strategy% (24690)------------------------------
% 1.40/0.55  % (24690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24690)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24690)Memory used [KB]: 1663
% 1.40/0.55  % (24690)Time elapsed: 0.140 s
% 1.40/0.55  % (24690)------------------------------
% 1.40/0.55  % (24690)------------------------------
% 1.40/0.55  % (24686)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.55  % (24692)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.55  % (24689)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.55  % (24703)Refutation not found, incomplete strategy% (24703)------------------------------
% 1.40/0.55  % (24703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24703)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24703)Memory used [KB]: 6268
% 1.40/0.55  % (24703)Time elapsed: 0.144 s
% 1.40/0.55  % (24703)------------------------------
% 1.40/0.55  % (24703)------------------------------
% 1.40/0.55  % (24692)Refutation not found, incomplete strategy% (24692)------------------------------
% 1.40/0.55  % (24692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24692)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24692)Memory used [KB]: 10618
% 1.40/0.55  % (24692)Time elapsed: 0.139 s
% 1.40/0.55  % (24692)------------------------------
% 1.40/0.55  % (24692)------------------------------
% 1.40/0.55  % (24684)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % (24694)Refutation not found, incomplete strategy% (24694)------------------------------
% 1.40/0.55  % (24694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24694)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24694)Memory used [KB]: 1791
% 1.40/0.55  % (24694)Time elapsed: 0.141 s
% 1.40/0.55  % (24694)------------------------------
% 1.40/0.55  % (24694)------------------------------
% 1.40/0.55  % (24685)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (24689)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.57  % SZS output start Proof for theBenchmark
% 1.40/0.57  fof(f308,plain,(
% 1.40/0.57    $false),
% 1.40/0.57    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f74,f126,f132,f136,f146,f154,f171,f180,f202,f207,f216,f224,f235,f242,f251,f264,f269,f277,f281,f293,f296,f298,f306])).
% 1.40/0.57  fof(f306,plain,(
% 1.40/0.57    ~spl14_13),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f300])).
% 1.40/0.57  fof(f300,plain,(
% 1.40/0.57    $false | ~spl14_13),
% 1.40/0.57    inference(unit_resulting_resolution,[],[f44,f44,f176,f97])).
% 1.40/0.57  fof(f97,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(X2)) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.57    inference(condensation,[],[f96])).
% 1.40/0.57  fof(f96,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,k1_tarski(X2)) | ~r2_hidden(X0,X3)) )),
% 1.40/0.57    inference(condensation,[],[f95])).
% 1.40/0.57  fof(f95,plain,(
% 1.40/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X2,X3) | ~r2_hidden(X0,X4) | ~r2_hidden(X1,X3) | ~r2_hidden(X1,k1_tarski(X2)) | ~r2_hidden(X0,X5)) )),
% 1.40/0.57    inference(superposition,[],[f82,f84])).
% 1.40/0.57  fof(f84,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k4_tarski(X0,X2)) = X3 | ~r2_hidden(X2,k1_tarski(X3)) | ~r2_hidden(X0,X1)) )),
% 1.40/0.57    inference(resolution,[],[f82,f42])).
% 1.40/0.57  fof(f42,plain,(
% 1.40/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.40/0.57    inference(equality_resolution,[],[f18])).
% 1.40/0.57  fof(f18,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.40/0.57    inference(cnf_transformation,[],[f1])).
% 1.40/0.57  fof(f1,axiom,(
% 1.40/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.40/0.57  fof(f82,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_mcart_1(k4_tarski(X2,X0)),X1) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 1.40/0.57    inference(resolution,[],[f46,f24])).
% 1.40/0.57  fof(f24,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f11])).
% 1.40/0.57  fof(f11,plain,(
% 1.40/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.40/0.57    inference(ennf_transformation,[],[f7])).
% 1.40/0.57  fof(f7,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.40/0.57  fof(f46,plain,(
% 1.40/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.40/0.57    inference(equality_resolution,[],[f45])).
% 1.40/0.57  fof(f45,plain,(
% 1.40/0.57    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.40/0.57    inference(equality_resolution,[],[f32])).
% 1.40/0.57  fof(f32,plain,(
% 1.40/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.40/0.57    inference(cnf_transformation,[],[f2])).
% 1.40/0.57  fof(f2,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.40/0.57  fof(f176,plain,(
% 1.40/0.57    ( ! [X1] : (~r2_hidden(k4_tarski(sK0,sK1),X1)) ) | ~spl14_13),
% 1.40/0.57    inference(avatar_component_clause,[],[f175])).
% 1.40/0.57  fof(f175,plain,(
% 1.40/0.57    spl14_13 <=> ! [X1] : ~r2_hidden(k4_tarski(sK0,sK1),X1)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).
% 1.40/0.57  % (24696)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.58  % (24688)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.58  fof(f44,plain,(
% 1.40/0.58    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.40/0.58    inference(equality_resolution,[],[f43])).
% 1.40/0.58  fof(f43,plain,(
% 1.40/0.58    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.40/0.58    inference(equality_resolution,[],[f17])).
% 1.40/0.58  fof(f17,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.40/0.58    inference(cnf_transformation,[],[f1])).
% 1.40/0.58  fof(f298,plain,(
% 1.40/0.58    spl14_3 | ~spl14_14),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f297])).
% 1.40/0.58  fof(f297,plain,(
% 1.40/0.58    $false | (spl14_3 | ~spl14_14)),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f61,f179])).
% 1.40/0.58  fof(f179,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(sK2,k1_tarski(X0)) | r2_hidden(X0,sK6)) ) | ~spl14_14),
% 1.40/0.58    inference(avatar_component_clause,[],[f178])).
% 1.40/0.58  fof(f178,plain,(
% 1.40/0.58    spl14_14 <=> ! [X0] : (r2_hidden(X0,sK6) | ~r2_hidden(sK2,k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 1.40/0.58  fof(f61,plain,(
% 1.40/0.58    ~r2_hidden(sK2,sK6) | spl14_3),
% 1.40/0.58    inference(avatar_component_clause,[],[f60])).
% 1.40/0.58  fof(f60,plain,(
% 1.40/0.58    spl14_3 <=> r2_hidden(sK2,sK6)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 1.40/0.58  fof(f296,plain,(
% 1.40/0.58    spl14_2 | ~spl14_9),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f295])).
% 1.40/0.58  fof(f295,plain,(
% 1.40/0.58    $false | (spl14_2 | ~spl14_9)),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f56,f145])).
% 1.40/0.58  fof(f145,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(sK3,k1_tarski(X0)) | r2_hidden(X0,sK7)) ) | ~spl14_9),
% 1.40/0.58    inference(avatar_component_clause,[],[f144])).
% 1.40/0.58  fof(f144,plain,(
% 1.40/0.58    spl14_9 <=> ! [X0] : (r2_hidden(X0,sK7) | ~r2_hidden(sK3,k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 1.40/0.58  fof(f56,plain,(
% 1.40/0.58    ~r2_hidden(sK3,sK7) | spl14_2),
% 1.40/0.58    inference(avatar_component_clause,[],[f55])).
% 1.40/0.58  fof(f55,plain,(
% 1.40/0.58    spl14_2 <=> r2_hidden(sK3,sK7)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 1.40/0.58  fof(f293,plain,(
% 1.40/0.58    ~spl14_20),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f289])).
% 1.40/0.58  fof(f289,plain,(
% 1.40/0.58    $false | ~spl14_20),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f44,f231,f97])).
% 1.40/0.58  fof(f231,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(sK0,X1)) ) | ~spl14_20),
% 1.40/0.58    inference(avatar_component_clause,[],[f230])).
% 1.40/0.58  fof(f230,plain,(
% 1.40/0.58    spl14_20 <=> ! [X1] : ~r2_hidden(sK0,X1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).
% 1.40/0.58  fof(f281,plain,(
% 1.40/0.58    spl14_4 | ~spl14_21),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f280])).
% 1.40/0.58  fof(f280,plain,(
% 1.40/0.58    $false | (spl14_4 | ~spl14_21)),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f66,f234])).
% 1.40/0.58  fof(f234,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(sK1,k1_tarski(X0)) | r2_hidden(X0,sK5)) ) | ~spl14_21),
% 1.40/0.58    inference(avatar_component_clause,[],[f233])).
% 1.40/0.58  fof(f233,plain,(
% 1.40/0.58    spl14_21 <=> ! [X0] : (r2_hidden(X0,sK5) | ~r2_hidden(sK1,k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).
% 1.40/0.58  fof(f66,plain,(
% 1.40/0.58    ~r2_hidden(sK1,sK5) | spl14_4),
% 1.40/0.58    inference(avatar_component_clause,[],[f65])).
% 1.40/0.58  fof(f65,plain,(
% 1.40/0.58    spl14_4 <=> r2_hidden(sK1,sK5)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 1.40/0.58  fof(f277,plain,(
% 1.40/0.58    ~spl14_10),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f272])).
% 1.40/0.58  fof(f272,plain,(
% 1.40/0.58    $false | ~spl14_10),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f44,f162,f97])).
% 1.40/0.58  fof(f162,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(sK3,X1)) ) | ~spl14_10),
% 1.40/0.58    inference(avatar_component_clause,[],[f161])).
% 1.40/0.58  fof(f161,plain,(
% 1.40/0.58    spl14_10 <=> ! [X1] : ~r2_hidden(sK3,X1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 1.40/0.58  fof(f269,plain,(
% 1.40/0.58    spl14_5 | ~spl14_24),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f267])).
% 1.40/0.58  fof(f267,plain,(
% 1.40/0.58    $false | (spl14_5 | ~spl14_24)),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f71,f44,f250])).
% 1.40/0.58  fof(f250,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(sK0,k1_tarski(X0)) | r2_hidden(X0,sK4)) ) | ~spl14_24),
% 1.40/0.58    inference(avatar_component_clause,[],[f249])).
% 1.40/0.58  fof(f249,plain,(
% 1.40/0.58    spl14_24 <=> ! [X0] : (r2_hidden(X0,sK4) | ~r2_hidden(sK0,k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).
% 1.40/0.58  fof(f71,plain,(
% 1.40/0.58    ~r2_hidden(sK0,sK4) | spl14_5),
% 1.40/0.58    inference(avatar_component_clause,[],[f70])).
% 1.40/0.58  fof(f70,plain,(
% 1.40/0.58    spl14_5 <=> r2_hidden(sK0,sK4)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 1.40/0.58  fof(f264,plain,(
% 1.40/0.58    ~spl14_23),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f259])).
% 1.40/0.58  fof(f259,plain,(
% 1.40/0.58    $false | ~spl14_23),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f44,f247,f97])).
% 1.40/0.58  fof(f247,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(sK1,X1)) ) | ~spl14_23),
% 1.40/0.58    inference(avatar_component_clause,[],[f246])).
% 1.40/0.58  fof(f246,plain,(
% 1.40/0.58    spl14_23 <=> ! [X1] : ~r2_hidden(sK1,X1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).
% 1.40/0.58  fof(f251,plain,(
% 1.40/0.58    spl14_23 | spl14_24 | ~spl14_22),
% 1.40/0.58    inference(avatar_split_clause,[],[f244,f240,f249,f246])).
% 1.40/0.58  fof(f240,plain,(
% 1.40/0.58    spl14_22 <=> ! [X0] : (r2_hidden(k1_mcart_1(X0),sK4) | ~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).
% 1.40/0.58  fof(f244,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK4) | ~r2_hidden(sK1,X1) | ~r2_hidden(sK0,k1_tarski(X0))) ) | ~spl14_22),
% 1.40/0.58    inference(superposition,[],[f243,f87])).
% 1.40/0.58  fof(f87,plain,(
% 1.40/0.58    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X2)) = X1 | ~r2_hidden(X2,X3) | ~r2_hidden(X0,k1_tarski(X1))) )),
% 1.40/0.58    inference(resolution,[],[f83,f42])).
% 1.40/0.58  fof(f83,plain,(
% 1.40/0.58    ( ! [X6,X4,X7,X5] : (r2_hidden(k1_mcart_1(k4_tarski(X6,X4)),X7) | ~r2_hidden(X6,X7) | ~r2_hidden(X4,X5)) )),
% 1.40/0.58    inference(resolution,[],[f46,f23])).
% 1.40/0.58  fof(f23,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f11])).
% 1.40/0.58  fof(f243,plain,(
% 1.40/0.58    r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK4) | ~spl14_22),
% 1.40/0.58    inference(resolution,[],[f241,f44])).
% 1.40/0.58  fof(f241,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) | r2_hidden(k1_mcart_1(X0),sK4)) ) | ~spl14_22),
% 1.40/0.58    inference(avatar_component_clause,[],[f240])).
% 1.40/0.58  fof(f242,plain,(
% 1.40/0.58    spl14_18 | spl14_22 | ~spl14_17),
% 1.40/0.58    inference(avatar_split_clause,[],[f238,f205,f240,f211])).
% 1.40/0.58  fof(f211,plain,(
% 1.40/0.58    spl14_18 <=> ! [X1] : ~r2_hidden(sK2,X1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 1.40/0.58  fof(f205,plain,(
% 1.40/0.58    spl14_17 <=> ! [X0] : (r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 1.40/0.58  fof(f238,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X0),sK4) | ~r2_hidden(sK2,X1) | ~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0))) ) | ~spl14_17),
% 1.40/0.58    inference(superposition,[],[f237,f87])).
% 1.40/0.58  fof(f237,plain,(
% 1.40/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),sK4) | ~spl14_17),
% 1.40/0.58    inference(resolution,[],[f206,f44])).
% 1.40/0.58  fof(f206,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) | r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4)) ) | ~spl14_17),
% 1.40/0.58    inference(avatar_component_clause,[],[f205])).
% 1.40/0.58  fof(f235,plain,(
% 1.40/0.58    spl14_20 | spl14_21 | ~spl14_19),
% 1.40/0.58    inference(avatar_split_clause,[],[f228,f214,f233,f230])).
% 1.40/0.58  fof(f214,plain,(
% 1.40/0.58    spl14_19 <=> ! [X0] : (r2_hidden(k2_mcart_1(X0),sK5) | ~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 1.40/0.58  fof(f228,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK5) | ~r2_hidden(sK1,k1_tarski(X0)) | ~r2_hidden(sK0,X1)) ) | ~spl14_19),
% 1.40/0.58    inference(superposition,[],[f227,f84])).
% 1.40/0.58  fof(f227,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK5) | ~spl14_19),
% 1.40/0.58    inference(resolution,[],[f215,f44])).
% 1.40/0.58  fof(f215,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0)) | r2_hidden(k2_mcart_1(X0),sK5)) ) | ~spl14_19),
% 1.40/0.58    inference(avatar_component_clause,[],[f214])).
% 1.40/0.58  fof(f224,plain,(
% 1.40/0.58    ~spl14_18),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f219])).
% 1.40/0.58  fof(f219,plain,(
% 1.40/0.58    $false | ~spl14_18),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f44,f212,f97])).
% 1.40/0.58  fof(f212,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(sK2,X1)) ) | ~spl14_18),
% 1.40/0.58    inference(avatar_component_clause,[],[f211])).
% 1.40/0.58  fof(f216,plain,(
% 1.40/0.58    spl14_18 | spl14_19 | ~spl14_16),
% 1.40/0.58    inference(avatar_split_clause,[],[f209,f200,f214,f211])).
% 1.40/0.58  fof(f200,plain,(
% 1.40/0.58    spl14_16 <=> ! [X0] : (r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).
% 1.40/0.58  fof(f209,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(X0),sK5) | ~r2_hidden(sK2,X1) | ~r2_hidden(k4_tarski(sK0,sK1),k1_tarski(X0))) ) | ~spl14_16),
% 1.40/0.58    inference(superposition,[],[f208,f87])).
% 1.40/0.58  fof(f208,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),sK5) | ~spl14_16),
% 1.40/0.58    inference(resolution,[],[f201,f44])).
% 1.40/0.58  fof(f201,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) | r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5)) ) | ~spl14_16),
% 1.40/0.58    inference(avatar_component_clause,[],[f200])).
% 1.40/0.58  fof(f207,plain,(
% 1.40/0.58    spl14_10 | spl14_17 | ~spl14_1),
% 1.40/0.58    inference(avatar_split_clause,[],[f203,f51,f205,f161])).
% 1.40/0.58  fof(f51,plain,(
% 1.40/0.58    spl14_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.40/0.58  fof(f203,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK4) | ~r2_hidden(sK3,X1) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))) ) | ~spl14_1),
% 1.40/0.58    inference(superposition,[],[f192,f87])).
% 1.40/0.58  fof(f192,plain,(
% 1.40/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)))),sK4) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f158,f23])).
% 1.40/0.58  fof(f158,plain,(
% 1.40/0.58    r2_hidden(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),k2_zfmisc_1(sK4,sK5)) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f138,f23])).
% 1.40/0.58  fof(f138,plain,(
% 1.40/0.58    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f53,f23])).
% 1.40/0.58  fof(f53,plain,(
% 1.40/0.58    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl14_1),
% 1.40/0.58    inference(avatar_component_clause,[],[f51])).
% 1.40/0.58  fof(f202,plain,(
% 1.40/0.58    spl14_10 | spl14_16 | ~spl14_1),
% 1.40/0.58    inference(avatar_split_clause,[],[f198,f51,f200,f161])).
% 1.40/0.58  fof(f198,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK5) | ~r2_hidden(sK3,X1) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))) ) | ~spl14_1),
% 1.40/0.58    inference(superposition,[],[f191,f87])).
% 1.40/0.58  fof(f191,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)))),sK5) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f158,f24])).
% 1.40/0.58  fof(f180,plain,(
% 1.40/0.58    spl14_13 | spl14_14 | ~spl14_12),
% 1.40/0.58    inference(avatar_split_clause,[],[f173,f169,f178,f175])).
% 1.40/0.58  fof(f169,plain,(
% 1.40/0.58    spl14_12 <=> ! [X0] : (r2_hidden(k2_mcart_1(X0),sK6) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 1.40/0.58  fof(f173,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK6) | ~r2_hidden(sK2,k1_tarski(X0)) | ~r2_hidden(k4_tarski(sK0,sK1),X1)) ) | ~spl14_12),
% 1.40/0.58    inference(superposition,[],[f172,f84])).
% 1.40/0.58  fof(f172,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK6) | ~spl14_12),
% 1.40/0.58    inference(resolution,[],[f170,f44])).
% 1.40/0.58  fof(f170,plain,(
% 1.40/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0)) | r2_hidden(k2_mcart_1(X0),sK6)) ) | ~spl14_12),
% 1.40/0.58    inference(avatar_component_clause,[],[f169])).
% 1.40/0.58  fof(f171,plain,(
% 1.40/0.58    spl14_10 | spl14_12 | ~spl14_1),
% 1.40/0.58    inference(avatar_split_clause,[],[f167,f51,f169,f161])).
% 1.40/0.58  fof(f167,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(X0),sK6) | ~r2_hidden(sK3,X1) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k1_tarski(X0))) ) | ~spl14_1),
% 1.40/0.58    inference(superposition,[],[f157,f87])).
% 1.40/0.58  fof(f157,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),sK6) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f138,f24])).
% 1.40/0.58  fof(f154,plain,(
% 1.40/0.58    ~spl14_8),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f148])).
% 1.40/0.58  fof(f148,plain,(
% 1.40/0.58    $false | ~spl14_8),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f44,f44,f142,f97])).
% 1.40/0.58  fof(f142,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1)) ) | ~spl14_8),
% 1.40/0.58    inference(avatar_component_clause,[],[f141])).
% 1.40/0.58  fof(f141,plain,(
% 1.40/0.58    spl14_8 <=> ! [X1] : ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 1.40/0.58  fof(f146,plain,(
% 1.40/0.58    spl14_8 | spl14_9 | ~spl14_1),
% 1.40/0.58    inference(avatar_split_clause,[],[f139,f51,f144,f141])).
% 1.40/0.58  fof(f139,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK7) | ~r2_hidden(sK3,k1_tarski(X0)) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X1)) ) | ~spl14_1),
% 1.40/0.58    inference(superposition,[],[f137,f84])).
% 1.40/0.58  fof(f137,plain,(
% 1.40/0.58    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),sK7) | ~spl14_1),
% 1.40/0.58    inference(resolution,[],[f53,f24])).
% 1.40/0.58  fof(f136,plain,(
% 1.40/0.58    ~spl14_5 | ~spl14_4 | spl14_7),
% 1.40/0.58    inference(avatar_split_clause,[],[f134,f129,f65,f70])).
% 1.40/0.58  fof(f129,plain,(
% 1.40/0.58    spl14_7 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 1.40/0.58  fof(f134,plain,(
% 1.40/0.58    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | spl14_7),
% 1.40/0.58    inference(resolution,[],[f131,f46])).
% 1.40/0.58  fof(f131,plain,(
% 1.40/0.58    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl14_7),
% 1.40/0.58    inference(avatar_component_clause,[],[f129])).
% 1.40/0.58  fof(f132,plain,(
% 1.40/0.58    ~spl14_7 | ~spl14_3 | spl14_6),
% 1.40/0.58    inference(avatar_split_clause,[],[f127,f123,f60,f129])).
% 1.40/0.58  fof(f123,plain,(
% 1.40/0.58    spl14_6 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 1.40/0.58  fof(f127,plain,(
% 1.40/0.58    ~r2_hidden(sK2,sK6) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl14_6),
% 1.40/0.58    inference(resolution,[],[f125,f46])).
% 1.40/0.58  fof(f125,plain,(
% 1.40/0.58    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl14_6),
% 1.40/0.58    inference(avatar_component_clause,[],[f123])).
% 1.40/0.58  fof(f126,plain,(
% 1.40/0.58    ~spl14_6 | ~spl14_2 | spl14_1),
% 1.40/0.58    inference(avatar_split_clause,[],[f121,f51,f55,f123])).
% 1.40/0.58  fof(f121,plain,(
% 1.40/0.58    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl14_1),
% 1.40/0.58    inference(resolution,[],[f52,f46])).
% 1.40/0.58  fof(f52,plain,(
% 1.40/0.58    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl14_1),
% 1.40/0.58    inference(avatar_component_clause,[],[f51])).
% 1.40/0.58  fof(f74,plain,(
% 1.40/0.58    ~spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | ~spl14_5),
% 1.40/0.58    inference(avatar_split_clause,[],[f41,f70,f65,f60,f55,f51])).
% 1.40/0.58  fof(f41,plain,(
% 1.40/0.58    ~r2_hidden(sK0,sK4) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    inference(definition_unfolding,[],[f12,f35,f36])).
% 1.40/0.58  fof(f36,plain,(
% 1.40/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f34,f22])).
% 1.40/0.58  fof(f22,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f4])).
% 1.40/0.58  fof(f4,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.40/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.40/0.58  fof(f34,plain,(
% 1.40/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f6])).
% 1.40/0.58  fof(f6,axiom,(
% 1.40/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.40/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.40/0.58  fof(f35,plain,(
% 1.40/0.58    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f33,f21])).
% 1.40/0.58  fof(f21,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f3])).
% 1.40/0.58  fof(f3,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.40/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.40/0.58  fof(f33,plain,(
% 1.40/0.58    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f5])).
% 1.40/0.58  fof(f5,axiom,(
% 1.40/0.58    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.40/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.40/0.58  fof(f12,plain,(
% 1.40/0.58    ~r2_hidden(sK0,sK4) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.40/0.58    inference(cnf_transformation,[],[f10])).
% 1.40/0.58  fof(f10,plain,(
% 1.40/0.58    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.40/0.58    inference(ennf_transformation,[],[f9])).
% 1.40/0.58  fof(f9,negated_conjecture,(
% 1.40/0.58    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.40/0.58    inference(negated_conjecture,[],[f8])).
% 1.40/0.58  fof(f8,conjecture,(
% 1.40/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.40/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).
% 1.40/0.58  fof(f73,plain,(
% 1.40/0.58    spl14_1 | spl14_5),
% 1.40/0.58    inference(avatar_split_clause,[],[f40,f70,f51])).
% 1.40/0.58  fof(f40,plain,(
% 1.40/0.58    r2_hidden(sK0,sK4) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    inference(definition_unfolding,[],[f13,f35,f36])).
% 1.40/0.58  fof(f13,plain,(
% 1.40/0.58    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.40/0.58    inference(cnf_transformation,[],[f10])).
% 1.40/0.58  fof(f68,plain,(
% 1.40/0.58    spl14_1 | spl14_4),
% 1.40/0.58    inference(avatar_split_clause,[],[f39,f65,f51])).
% 1.40/0.58  fof(f39,plain,(
% 1.40/0.58    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    inference(definition_unfolding,[],[f14,f35,f36])).
% 1.40/0.58  fof(f14,plain,(
% 1.40/0.58    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.40/0.58    inference(cnf_transformation,[],[f10])).
% 1.40/0.58  fof(f63,plain,(
% 1.40/0.58    spl14_1 | spl14_3),
% 1.40/0.58    inference(avatar_split_clause,[],[f38,f60,f51])).
% 1.40/0.58  fof(f38,plain,(
% 1.40/0.58    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    inference(definition_unfolding,[],[f15,f35,f36])).
% 1.40/0.58  fof(f15,plain,(
% 1.40/0.58    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.40/0.58    inference(cnf_transformation,[],[f10])).
% 1.40/0.58  fof(f58,plain,(
% 1.40/0.58    spl14_1 | spl14_2),
% 1.40/0.58    inference(avatar_split_clause,[],[f37,f55,f51])).
% 1.40/0.58  fof(f37,plain,(
% 1.40/0.58    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.40/0.58    inference(definition_unfolding,[],[f16,f35,f36])).
% 1.40/0.58  fof(f16,plain,(
% 1.40/0.58    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.40/0.58    inference(cnf_transformation,[],[f10])).
% 1.40/0.58  % SZS output end Proof for theBenchmark
% 1.40/0.58  % (24689)------------------------------
% 1.40/0.58  % (24689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (24689)Termination reason: Refutation
% 1.40/0.58  
% 1.40/0.58  % (24689)Memory used [KB]: 6396
% 1.40/0.58  % (24689)Time elapsed: 0.152 s
% 1.40/0.58  % (24689)------------------------------
% 1.40/0.58  % (24689)------------------------------
% 1.40/0.58  % (24675)Success in time 0.212 s
%------------------------------------------------------------------------------
