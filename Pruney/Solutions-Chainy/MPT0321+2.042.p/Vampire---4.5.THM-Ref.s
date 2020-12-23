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
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 215 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :    7
%              Number of atoms          :  276 ( 566 expanded)
%              Number of equality atoms :   37 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f66,f71,f83,f107,f132,f137,f158,f172,f195,f207,f231,f259,f303,f307,f348,f352,f360,f380])).

fof(f380,plain,
    ( spl9_1
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl9_1
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f22,f51,f364,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

% (30122)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f364,plain,
    ( ! [X2] : ~ r2_xboole_0(X2,sK0)
    | ~ spl9_10 ),
    inference(resolution,[],[f106,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f106,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_10
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f51,plain,
    ( k1_xboole_0 != sK0
    | spl9_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f360,plain,
    ( spl9_16
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f354,f170,f155])).

fof(f155,plain,
    ( spl9_16
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f170,plain,
    ( spl9_19
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f354,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_19 ),
    inference(resolution,[],[f171,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f171,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f352,plain,
    ( spl9_3
    | ~ spl9_23
    | spl9_27 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | spl9_3
    | ~ spl9_23
    | spl9_27 ),
    inference(unit_resulting_resolution,[],[f230,f61,f347,f29])).

fof(f347,plain,
    ( ~ r2_xboole_0(sK1,sK3)
    | spl9_27 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl9_27
  <=> r2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f61,plain,
    ( sK1 != sK3
    | spl9_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f230,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f228])).

% (30116)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f228,plain,
    ( spl9_23
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f348,plain,
    ( ~ spl9_27
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f343,f193,f345])).

fof(f193,plain,
    ( spl9_22
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f343,plain,
    ( ~ r2_xboole_0(sK1,sK3)
    | ~ spl9_22 ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( ~ r2_xboole_0(sK1,sK3)
    | ~ r2_xboole_0(sK1,sK3)
    | ~ spl9_22 ),
    inference(resolution,[],[f279,f33])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK1,X0),sK3)
        | ~ r2_xboole_0(sK1,X0) )
    | ~ spl9_22 ),
    inference(resolution,[],[f194,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f194,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f307,plain,
    ( ~ spl9_13
    | spl9_4
    | spl9_25 ),
    inference(avatar_split_clause,[],[f305,f300,f63,f129])).

fof(f129,plain,
    ( spl9_13
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f63,plain,
    ( spl9_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f300,plain,
    ( spl9_25
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f305,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2)
    | spl9_25 ),
    inference(resolution,[],[f302,f29])).

fof(f302,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl9_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f303,plain,
    ( ~ spl9_25
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f298,f167,f300])).

fof(f167,plain,
    ( spl9_18
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f298,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | ~ spl9_18 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK2)
    | ~ spl9_18 ),
    inference(resolution,[],[f176,f33])).

fof(f176,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK7(sK0,X2),sK2)
        | ~ r2_xboole_0(sK0,X2) )
    | ~ spl9_18 ),
    inference(resolution,[],[f168,f34])).

fof(f168,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f259,plain,
    ( spl9_2
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl9_2
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f22,f56,f240,f29])).

fof(f240,plain,
    ( ! [X2] : ~ r2_xboole_0(X2,sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f79,f33])).

fof(f79,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl9_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f231,plain,
    ( spl9_23
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f191,f135,f228])).

fof(f135,plain,
    ( spl9_14
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f191,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f152,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f152,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK3),sK1)
        | r1_tarski(X3,sK3) )
    | ~ spl9_14 ),
    inference(resolution,[],[f136,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f207,plain,
    ( spl9_9
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f199,f182,f101])).

fof(f101,plain,
    ( spl9_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

% (30121)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f182,plain,
    ( spl9_20
  <=> ! [X3] : ~ r2_hidden(X3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f199,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_20 ),
    inference(resolution,[],[f183,f23])).

fof(f183,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f195,plain,
    ( spl9_20
    | spl9_22
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f113,f68,f193,f182])).

fof(f68,plain,
    ( spl9_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f113,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X6,sK1) )
    | ~ spl9_5 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f74,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl9_5 ),
    inference(superposition,[],[f43,f70])).

fof(f70,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f172,plain,
    ( spl9_18
    | spl9_19
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f112,f68,f170,f167])).

fof(f112,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f158,plain,
    ( ~ spl9_16
    | spl9_6
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f150,f135,f78,f155])).

fof(f150,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ v1_xboole_0(sK3) )
    | ~ spl9_14 ),
    inference(resolution,[],[f136,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f137,plain,
    ( spl9_10
    | spl9_14
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f76,f68,f135,f105])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f73,f43])).

fof(f73,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f42,f70])).

fof(f132,plain,
    ( spl9_13
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f127,f81,f129])).

fof(f81,plain,
    ( spl9_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f127,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f98,f31])).

fof(f98,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK2),sK0)
        | r1_tarski(X3,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f82,f32])).

fof(f82,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f107,plain,
    ( ~ spl9_9
    | spl9_10
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f96,f81,f105,f101])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ v1_xboole_0(sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f82,f24])).

fof(f83,plain,
    ( spl9_6
    | spl9_7
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f75,f68,f81,f78])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f72,f43])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl9_5 ),
    inference(superposition,[],[f41,f70])).

fof(f71,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f18,f68])).

fof(f18,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

% (30110)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f66,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f17,f63,f59])).

fof(f17,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:38:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (30111)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (30107)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (30117)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (30109)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (30100)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30103)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (30119)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (30101)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (30095)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (30095)Refutation not found, incomplete strategy% (30095)------------------------------
% 0.21/0.53  % (30095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30095)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30095)Memory used [KB]: 1663
% 0.21/0.53  % (30095)Time elapsed: 0.103 s
% 0.21/0.53  % (30095)------------------------------
% 0.21/0.53  % (30095)------------------------------
% 0.21/0.54  % (30098)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (30118)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (30097)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (30108)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (30099)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (30096)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (30117)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f52,f57,f66,f71,f83,f107,f132,f137,f158,f172,f195,f207,f231,f259,f303,f307,f348,f352,f360,f380])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    spl9_1 | ~spl9_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    $false | (spl9_1 | ~spl9_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f22,f51,f364,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  % (30122)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    ( ! [X2] : (~r2_xboole_0(X2,sK0)) ) | ~spl9_10),
% 0.21/0.54    inference(resolution,[],[f106,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl9_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl9_10 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl9_1 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f360,plain,(
% 0.21/0.55    spl9_16 | ~spl9_19),
% 0.21/0.55    inference(avatar_split_clause,[],[f354,f170,f155])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    spl9_16 <=> v1_xboole_0(sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    spl9_19 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.55  fof(f354,plain,(
% 0.21/0.55    v1_xboole_0(sK3) | ~spl9_19),
% 0.21/0.55    inference(resolution,[],[f171,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl9_19),
% 0.21/0.55    inference(avatar_component_clause,[],[f170])).
% 0.21/0.55  fof(f352,plain,(
% 0.21/0.55    spl9_3 | ~spl9_23 | spl9_27),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f350])).
% 0.21/0.55  fof(f350,plain,(
% 0.21/0.55    $false | (spl9_3 | ~spl9_23 | spl9_27)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f230,f61,f347,f29])).
% 0.21/0.55  fof(f347,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK3) | spl9_27),
% 0.21/0.55    inference(avatar_component_clause,[],[f345])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    spl9_27 <=> r2_xboole_0(sK1,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    sK1 != sK3 | spl9_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl9_3 <=> sK1 = sK3),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    r1_tarski(sK1,sK3) | ~spl9_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f228])).
% 0.21/0.55  % (30116)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    spl9_23 <=> r1_tarski(sK1,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    ~spl9_27 | ~spl9_22),
% 0.21/0.55    inference(avatar_split_clause,[],[f343,f193,f345])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    spl9_22 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK3) | ~spl9_22),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f341])).
% 0.21/0.55  fof(f341,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK3) | ~r2_xboole_0(sK1,sK3) | ~spl9_22),
% 0.21/0.55    inference(resolution,[],[f279,f33])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK7(sK1,X0),sK3) | ~r2_xboole_0(sK1,X0)) ) | ~spl9_22),
% 0.21/0.55    inference(resolution,[],[f194,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl9_22),
% 0.21/0.55    inference(avatar_component_clause,[],[f193])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    ~spl9_13 | spl9_4 | spl9_25),
% 0.21/0.55    inference(avatar_split_clause,[],[f305,f300,f63,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    spl9_13 <=> r1_tarski(sK0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    spl9_4 <=> sK0 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    spl9_25 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    sK0 = sK2 | ~r1_tarski(sK0,sK2) | spl9_25),
% 0.21/0.55    inference(resolution,[],[f302,f29])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ~r2_xboole_0(sK0,sK2) | spl9_25),
% 0.21/0.55    inference(avatar_component_clause,[],[f300])).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    ~spl9_25 | ~spl9_18),
% 0.21/0.55    inference(avatar_split_clause,[],[f298,f167,f300])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    spl9_18 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    ~r2_xboole_0(sK0,sK2) | ~spl9_18),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f296])).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    ~r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK2) | ~spl9_18),
% 0.21/0.55    inference(resolution,[],[f176,f33])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(sK7(sK0,X2),sK2) | ~r2_xboole_0(sK0,X2)) ) | ~spl9_18),
% 0.21/0.55    inference(resolution,[],[f168,f34])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl9_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f167])).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    spl9_2 | ~spl9_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    $false | (spl9_2 | ~spl9_6)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f22,f56,f240,f29])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_xboole_0(X2,sK1)) ) | ~spl9_6),
% 0.21/0.55    inference(resolution,[],[f79,f33])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl9_6 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl9_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl9_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    spl9_23 | ~spl9_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f191,f135,f228])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    spl9_14 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    r1_tarski(sK1,sK3) | ~spl9_14),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl9_14),
% 0.21/0.55    inference(resolution,[],[f152,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(sK6(X3,sK3),sK1) | r1_tarski(X3,sK3)) ) | ~spl9_14),
% 0.21/0.55    inference(resolution,[],[f136,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl9_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f135])).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    spl9_9 | ~spl9_20),
% 0.21/0.55    inference(avatar_split_clause,[],[f199,f182,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl9_9 <=> v1_xboole_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.55  % (30121)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    spl9_20 <=> ! [X3] : ~r2_hidden(X3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    v1_xboole_0(sK2) | ~spl9_20),
% 0.21/0.55    inference(resolution,[],[f183,f23])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,sK2)) ) | ~spl9_20),
% 0.21/0.55    inference(avatar_component_clause,[],[f182])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    spl9_20 | spl9_22 | ~spl9_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f113,f68,f193,f182])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl9_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) ) | ~spl9_5),
% 0.21/0.55    inference(resolution,[],[f74,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) ) | ~spl9_5),
% 0.21/0.55    inference(superposition,[],[f43,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl9_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f68])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    spl9_18 | spl9_19 | ~spl9_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f112,f68,f170,f167])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | ~spl9_5),
% 0.21/0.55    inference(resolution,[],[f74,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ~spl9_16 | spl9_6 | ~spl9_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f150,f135,f78,f155])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | ~v1_xboole_0(sK3)) ) | ~spl9_14),
% 0.21/0.55    inference(resolution,[],[f136,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    spl9_10 | spl9_14 | ~spl9_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f76,f68,f135,f105])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl9_5),
% 0.21/0.55    inference(resolution,[],[f73,f43])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) ) | ~spl9_5),
% 0.21/0.55    inference(superposition,[],[f42,f70])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl9_13 | ~spl9_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f127,f81,f129])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    spl9_7 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    r1_tarski(sK0,sK2) | ~spl9_7),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl9_7),
% 0.21/0.55    inference(resolution,[],[f98,f31])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(sK6(X3,sK2),sK0) | r1_tarski(X3,sK2)) ) | ~spl9_7),
% 0.21/0.55    inference(resolution,[],[f82,f32])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl9_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f81])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ~spl9_9 | spl9_10 | ~spl9_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f96,f81,f105,f101])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_xboole_0(sK2)) ) | ~spl9_7),
% 0.21/0.55    inference(resolution,[],[f82,f24])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    spl9_6 | spl9_7 | ~spl9_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f75,f68,f81,f78])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl9_5),
% 0.21/0.55    inference(resolution,[],[f72,f43])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl9_5),
% 0.21/0.55    inference(superposition,[],[f41,f70])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl9_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f18,f68])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.55  % (30110)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ~spl9_3 | ~spl9_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f17,f63,f59])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    sK0 != sK2 | sK1 != sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ~spl9_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f20,f54])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~spl9_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f19,f49])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (30117)------------------------------
% 0.21/0.55  % (30117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30117)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (30117)Memory used [KB]: 10874
% 0.21/0.55  % (30117)Time elapsed: 0.088 s
% 0.21/0.55  % (30117)------------------------------
% 0.21/0.55  % (30117)------------------------------
% 0.21/0.55  % (30112)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (30124)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (30114)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (30094)Success in time 0.189 s
%------------------------------------------------------------------------------
