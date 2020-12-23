%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 175 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :    6
%              Number of atoms          :  309 ( 513 expanded)
%              Number of equality atoms :   52 (  93 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f60,f66,f79,f84,f100,f121,f132,f147,f155,f206,f270,f289,f316,f339,f342,f353,f368,f377,f392,f401])).

fof(f401,plain,
    ( spl8_4
    | ~ spl8_9
    | ~ spl8_51 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl8_4
    | ~ spl8_9
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f397,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f397,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_9
    | ~ spl8_51 ),
    inference(resolution,[],[f391,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f391,plain,
    ( ! [X0] : r1_xboole_0(sK0,X0)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl8_51
  <=> ! [X0] : r1_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f392,plain,
    ( spl8_51
    | ~ spl8_10
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f378,f348,f82,f390])).

fof(f82,plain,
    ( spl8_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f348,plain,
    ( spl8_48
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f378,plain,
    ( ! [X0] : r1_xboole_0(sK0,X0)
    | ~ spl8_10
    | ~ spl8_48 ),
    inference(resolution,[],[f349,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f349,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f348])).

fof(f377,plain,
    ( spl8_2
    | ~ spl8_9
    | ~ spl8_50 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl8_2
    | ~ spl8_9
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f373,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f373,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9
    | ~ spl8_50 ),
    inference(resolution,[],[f367,f78])).

fof(f367,plain,
    ( ! [X0] : r1_xboole_0(sK1,X0)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl8_50
  <=> ! [X0] : r1_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f368,plain,
    ( spl8_50
    | ~ spl8_10
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f354,f351,f82,f366])).

fof(f351,plain,
    ( spl8_49
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f354,plain,
    ( ! [X0] : r1_xboole_0(sK1,X0)
    | ~ spl8_10
    | ~ spl8_49 ),
    inference(resolution,[],[f352,f83])).

fof(f352,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl8_48
    | spl8_49
    | ~ spl8_6
    | ~ spl8_20
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f346,f314,f130,f62,f351,f348])).

fof(f62,plain,
    ( spl8_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f130,plain,
    ( spl8_20
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f314,plain,
    ( spl8_46
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_6
    | ~ spl8_20
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f343,f315])).

fof(f315,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f314])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(superposition,[],[f131,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f131,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X5,X1)
        | ~ r2_hidden(X4,X0) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f342,plain,
    ( spl8_1
    | ~ spl8_24
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl8_1
    | ~ spl8_24
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f315,f315,f45,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_24
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f45,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f339,plain,
    ( spl8_3
    | ~ spl8_23
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl8_3
    | ~ spl8_23
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f52,f315,f315,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_23
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f52,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f316,plain,
    ( spl8_46
    | ~ spl8_20
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f310,f287,f130,f314])).

fof(f287,plain,
    ( spl8_44
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f310,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_20
    | ~ spl8_44 ),
    inference(condensation,[],[f298])).

fof(f298,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl8_20
    | ~ spl8_44 ),
    inference(resolution,[],[f288,f131])).

fof(f288,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( spl8_44
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f277,f268,f58,f287])).

fof(f58,plain,
    ( spl8_5
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f268,plain,
    ( spl8_41
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(X2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f277,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(resolution,[],[f269,f59])).

fof(f59,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f58])).

% (16593)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f269,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( spl8_41
    | ~ spl8_18
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f208,f204,f119,f268])).

fof(f119,plain,
    ( spl8_18
  <=> ! [X1,X3,X0] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f204,plain,
    ( spl8_32
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r2_hidden(sK5(X1,X2,X0),X3)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(X2,X2) )
    | ~ spl8_18
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(X2,X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl8_18
    | ~ spl8_32 ),
    inference(resolution,[],[f205,f120])).

fof(f120,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f205,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK5(X1,X2,X0),X3)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl8_32
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f127,f119,f98,f204])).

fof(f98,plain,
    ( spl8_14
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f127,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ r2_hidden(sK5(X1,X2,X0),X3)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(resolution,[],[f120,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f155,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f26,f153])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f147,plain,(
    spl8_23 ),
    inference(avatar_split_clause,[],[f25,f145])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f132,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f37,f130])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f121,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f39,f119])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f19,f98])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f84,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f20,f82])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f17,f77])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f66,plain,
    ( spl8_6
    | spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f15,f54,f47,f62])).

fof(f15,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f60,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f35,f58])).

fof(f35,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f42,f54,f51])).

fof(f42,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f41,f47,f44])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (16584)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (16590)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (16576)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (16581)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (16576)Refutation not found, incomplete strategy% (16576)------------------------------
% 0.20/0.49  % (16576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16576)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16576)Memory used [KB]: 6140
% 0.20/0.49  % (16576)Time elapsed: 0.061 s
% 0.20/0.49  % (16576)------------------------------
% 0.20/0.49  % (16576)------------------------------
% 0.20/0.49  % (16580)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (16591)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (16582)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (16577)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (16577)Refutation not found, incomplete strategy% (16577)------------------------------
% 0.20/0.50  % (16577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16577)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16577)Memory used [KB]: 10618
% 0.20/0.50  % (16577)Time elapsed: 0.082 s
% 0.20/0.50  % (16577)------------------------------
% 0.20/0.50  % (16577)------------------------------
% 0.20/0.50  % (16583)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (16595)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (16585)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (16594)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (16578)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (16579)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (16596)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (16596)Refutation not found, incomplete strategy% (16596)------------------------------
% 0.20/0.51  % (16596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16596)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16596)Memory used [KB]: 10618
% 0.20/0.51  % (16596)Time elapsed: 0.101 s
% 0.20/0.51  % (16596)------------------------------
% 0.20/0.51  % (16596)------------------------------
% 0.20/0.51  % (16588)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (16589)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (16585)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f402,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f49,f56,f60,f66,f79,f84,f100,f121,f132,f147,f155,f206,f270,f289,f316,f339,f342,f353,f368,f377,f392,f401])).
% 0.20/0.51  fof(f401,plain,(
% 0.20/0.51    spl8_4 | ~spl8_9 | ~spl8_51),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f400])).
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    $false | (spl8_4 | ~spl8_9 | ~spl8_51)),
% 0.20/0.51    inference(subsumption_resolution,[],[f397,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl8_4 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f397,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | (~spl8_9 | ~spl8_51)),
% 0.20/0.51    inference(resolution,[],[f391,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) ) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl8_9 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(sK0,X0)) ) | ~spl8_51),
% 0.20/0.51    inference(avatar_component_clause,[],[f390])).
% 0.20/0.51  fof(f390,plain,(
% 0.20/0.51    spl8_51 <=> ! [X0] : r1_xboole_0(sK0,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    spl8_51 | ~spl8_10 | ~spl8_48),
% 0.20/0.51    inference(avatar_split_clause,[],[f378,f348,f82,f390])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl8_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    spl8_48 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.20/0.51  fof(f378,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(sK0,X0)) ) | (~spl8_10 | ~spl8_48)),
% 0.20/0.51    inference(resolution,[],[f349,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_48),
% 0.20/0.51    inference(avatar_component_clause,[],[f348])).
% 0.20/0.51  fof(f377,plain,(
% 0.20/0.51    spl8_2 | ~spl8_9 | ~spl8_50),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f376])).
% 0.20/0.51  fof(f376,plain,(
% 0.20/0.51    $false | (spl8_2 | ~spl8_9 | ~spl8_50)),
% 0.20/0.51    inference(subsumption_resolution,[],[f373,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl8_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f373,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | (~spl8_9 | ~spl8_50)),
% 0.20/0.51    inference(resolution,[],[f367,f78])).
% 0.20/0.51  fof(f367,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(sK1,X0)) ) | ~spl8_50),
% 0.20/0.51    inference(avatar_component_clause,[],[f366])).
% 0.20/0.51  fof(f366,plain,(
% 0.20/0.51    spl8_50 <=> ! [X0] : r1_xboole_0(sK1,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.51  fof(f368,plain,(
% 0.20/0.51    spl8_50 | ~spl8_10 | ~spl8_49),
% 0.20/0.51    inference(avatar_split_clause,[],[f354,f351,f82,f366])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    spl8_49 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(sK1,X0)) ) | (~spl8_10 | ~spl8_49)),
% 0.20/0.51    inference(resolution,[],[f352,f83])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_49),
% 0.20/0.51    inference(avatar_component_clause,[],[f351])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    spl8_48 | spl8_49 | ~spl8_6 | ~spl8_20 | ~spl8_46),
% 0.20/0.51    inference(avatar_split_clause,[],[f346,f314,f130,f62,f351,f348])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl8_6 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl8_20 <=> ! [X1,X5,X0,X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.51  fof(f314,plain,(
% 0.20/0.51    spl8_46 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl8_6 | ~spl8_20 | ~spl8_46)),
% 0.20/0.51    inference(subsumption_resolution,[],[f343,f315])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_46),
% 0.20/0.51    inference(avatar_component_clause,[],[f314])).
% 0.20/0.51  fof(f343,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl8_6 | ~spl8_20)),
% 0.20/0.51    inference(superposition,[],[f131,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) ) | ~spl8_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f130])).
% 0.20/0.51  fof(f342,plain,(
% 0.20/0.51    spl8_1 | ~spl8_24 | ~spl8_46),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f341])).
% 0.20/0.51  fof(f341,plain,(
% 0.20/0.51    $false | (spl8_1 | ~spl8_24 | ~spl8_46)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f315,f315,f45,f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl8_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f153])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl8_24 <=> ! [X1,X0,X2] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f339,plain,(
% 0.20/0.51    spl8_3 | ~spl8_23 | ~spl8_46),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f324])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    $false | (spl8_3 | ~spl8_23 | ~spl8_46)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f52,f315,f315,f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl8_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl8_23 <=> ! [X1,X0,X2] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f316,plain,(
% 0.20/0.51    spl8_46 | ~spl8_20 | ~spl8_44),
% 0.20/0.51    inference(avatar_split_clause,[],[f310,f287,f130,f314])).
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    spl8_44 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 0.20/0.51  fof(f310,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_20 | ~spl8_44)),
% 0.20/0.51    inference(condensation,[],[f298])).
% 0.20/0.51  fof(f298,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,X2)) ) | (~spl8_20 | ~spl8_44)),
% 0.20/0.51    inference(resolution,[],[f288,f131])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | ~spl8_44),
% 0.20/0.51    inference(avatar_component_clause,[],[f287])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    spl8_44 | ~spl8_5 | ~spl8_41),
% 0.20/0.51    inference(avatar_split_clause,[],[f277,f268,f58,f287])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl8_5 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    spl8_41 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(X2,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.20/0.52  fof(f277,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | (~spl8_5 | ~spl8_41)),
% 0.20/0.52    inference(resolution,[],[f269,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  % (16593)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) ) | ~spl8_41),
% 0.20/0.52    inference(avatar_component_clause,[],[f268])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    spl8_41 | ~spl8_18 | ~spl8_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f208,f204,f119,f268])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl8_18 <=> ! [X1,X3,X0] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    spl8_32 <=> ! [X1,X3,X0,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK5(X1,X2,X0),X3) | ~r1_xboole_0(X2,X3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(X2,X2)) ) | (~spl8_18 | ~spl8_32)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f207])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(X2,X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) ) | (~spl8_18 | ~spl8_32)),
% 0.20/0.52    inference(resolution,[],[f205,f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) ) | ~spl8_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f119])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X1,X2,X0),X3) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(X2,X3)) ) | ~spl8_32),
% 0.20/0.52    inference(avatar_component_clause,[],[f204])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    spl8_32 | ~spl8_14 | ~spl8_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f127,f119,f98,f204])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    spl8_14 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK5(X1,X2,X0),X3) | ~r1_xboole_0(X2,X3)) ) | (~spl8_14 | ~spl8_18)),
% 0.20/0.52    inference(resolution,[],[f120,f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl8_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f98])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl8_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f153])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl8_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f145])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl8_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f130])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl8_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f119])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl8_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f98])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl8_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f82])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl8_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f17,f77])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl8_6 | spl8_2 | spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f15,f54,f47,f62])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl8_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f58])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(equality_resolution,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ~spl8_3 | ~spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f54,f51])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.52    inference(inner_rewriting,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f47,f44])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.52    inference(inner_rewriting,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (16585)------------------------------
% 0.20/0.52  % (16585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16585)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (16585)Memory used [KB]: 10874
% 0.20/0.52  % (16585)Time elapsed: 0.096 s
% 0.20/0.52  % (16585)------------------------------
% 0.20/0.52  % (16585)------------------------------
% 0.20/0.52  % (16575)Success in time 0.152 s
%------------------------------------------------------------------------------
