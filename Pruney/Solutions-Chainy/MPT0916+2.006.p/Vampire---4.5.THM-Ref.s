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
% DateTime   : Thu Dec  3 12:59:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 251 expanded)
%              Number of leaves         :   38 ( 110 expanded)
%              Depth                    :    7
%              Number of atoms          :  355 ( 739 expanded)
%              Number of equality atoms :   55 (  95 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f78,f86,f94,f101,f106,f116,f124,f135,f153,f158,f177,f203,f222,f235,f254,f258,f272,f278,f299,f301,f324,f326,f352])).

fof(f352,plain,
    ( ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f100,f115,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f115,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_10
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f100,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_7
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f326,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f324,plain,
    ( ~ spl10_13
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_26 ),
    inference(unit_resulting_resolution,[],[f134,f202,f47])).

fof(f202,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl10_26
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f134,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_13
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f301,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f299,plain,
    ( ~ spl10_13
    | ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f134,f221,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f221,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl10_30
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f278,plain,(
    spl10_36 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl10_36 ),
    inference(unit_resulting_resolution,[],[f32,f56,f29,f271,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X2,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f271,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl10_36
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f272,plain,
    ( ~ spl10_36
    | spl10_29
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f265,f224,f216,f269])).

fof(f216,plain,
    ( spl10_29
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f224,plain,
    ( spl10_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f265,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_29
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f218,f226])).

fof(f226,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f224])).

fof(f218,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_29 ),
    inference(avatar_component_clause,[],[f216])).

fof(f258,plain,
    ( spl10_31
    | ~ spl10_8
    | spl10_32
    | spl10_33
    | ~ spl10_17
    | spl10_20 ),
    inference(avatar_split_clause,[],[f255,f170,f155,f232,f228,f103,f224])).

fof(f103,plain,
    ( spl10_8
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f228,plain,
    ( spl10_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f232,plain,
    ( spl10_33
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f155,plain,
    ( spl10_17
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f170,plain,
    ( spl10_20
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f255,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl10_20 ),
    inference(superposition,[],[f172,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f172,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl10_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f254,plain,
    ( spl10_31
    | ~ spl10_8
    | spl10_32
    | spl10_33
    | ~ spl10_16
    | spl10_21 ),
    inference(avatar_split_clause,[],[f247,f174,f150,f232,f228,f103,f224])).

fof(f150,plain,
    ( spl10_16
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f174,plain,
    ( spl10_21
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f247,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl10_21 ),
    inference(superposition,[],[f176,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f235,plain,
    ( spl10_31
    | ~ spl10_8
    | spl10_32
    | spl10_33
    | ~ spl10_11
    | spl10_19 ),
    inference(avatar_split_clause,[],[f195,f166,f121,f232,f228,f103,f224])).

fof(f121,plain,
    ( spl10_11
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f166,plain,
    ( spl10_19
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f195,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl10_19 ),
    inference(superposition,[],[f168,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f168,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f222,plain,
    ( ~ spl10_29
    | spl10_30
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f213,f91,f220,f216])).

fof(f91,plain,
    ( spl10_6
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f95,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

% (26381)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f95,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl10_6 ),
    inference(resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f93,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f203,plain,
    ( ~ spl10_25
    | spl10_26
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f193,f83,f201,f197])).

fof(f197,plain,
    ( spl10_25
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f83,plain,
    ( spl10_5
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_xboole_0(sK1) )
    | ~ spl10_5 ),
    inference(resolution,[],[f87,f31])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl10_5 ),
    inference(resolution,[],[f85,f39])).

fof(f85,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f177,plain,
    ( ~ spl10_19
    | ~ spl10_20
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f23,f174,f170,f166])).

fof(f23,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f158,plain,
    ( spl10_17
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f142,f132,f155])).

fof(f142,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl10_13 ),
    inference(resolution,[],[f134,f47])).

fof(f153,plain,
    ( spl10_16
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f141,f132,f150])).

fof(f141,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl10_13 ),
    inference(resolution,[],[f134,f46])).

fof(f135,plain,
    ( spl10_13
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f117,f98,f132])).

fof(f117,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl10_7 ),
    inference(resolution,[],[f100,f46])).

fof(f124,plain,
    ( spl10_11
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f118,f98,f121])).

fof(f118,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl10_7 ),
    inference(resolution,[],[f100,f47])).

fof(f116,plain,
    ( ~ spl10_9
    | spl10_10
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f107,f75,f114,f110])).

fof(f110,plain,
    ( spl10_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f75,plain,
    ( spl10_4
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5)
        | ~ v1_xboole_0(sK2) )
    | ~ spl10_4 ),
    inference(resolution,[],[f79,f31])).

fof(f79,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK5) )
    | ~ spl10_4 ),
    inference(resolution,[],[f77,f39])).

fof(f77,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f106,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f24,f44])).

fof(f24,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f25,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( spl10_6
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f89,f69,f91])).

fof(f69,plain,
    ( spl10_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f89,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f86,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f81,f64,f83])).

fof(f64,plain,
    ( spl10_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f81,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f78,plain,
    ( spl10_4
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f73,f59,f75])).

fof(f59,plain,
    ( spl10_1
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f73,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl10_1 ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f72,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (26358)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (26351)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (26360)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (26367)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (26377)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (26369)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (26355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26352)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (26354)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (26356)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (26353)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (26359)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (26362)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (26359)Refutation not found, incomplete strategy% (26359)------------------------------
% 0.21/0.52  % (26359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26359)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26359)Memory used [KB]: 10746
% 0.21/0.52  % (26359)Time elapsed: 0.105 s
% 0.21/0.52  % (26359)------------------------------
% 0.21/0.52  % (26359)------------------------------
% 0.21/0.52  % (26375)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (26373)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (26380)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (26368)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (26379)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (26378)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (26372)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (26374)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (26370)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (26366)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (26353)Refutation not found, incomplete strategy% (26353)------------------------------
% 0.21/0.54  % (26353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26353)Memory used [KB]: 10874
% 0.21/0.54  % (26353)Time elapsed: 0.109 s
% 0.21/0.54  % (26353)------------------------------
% 0.21/0.54  % (26353)------------------------------
% 0.21/0.54  % (26374)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f62,f67,f72,f78,f86,f94,f101,f106,f116,f124,f135,f153,f158,f177,f203,f222,f235,f254,f258,f272,f278,f299,f301,f324,f326,f352])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    ~spl10_7 | ~spl10_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f341])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    $false | (~spl10_7 | ~spl10_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f100,f115,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK5)) ) | ~spl10_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl10_10 <=> ! [X0] : ~r2_hidden(X0,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl10_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl10_7 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    ~spl10_13 | ~spl10_26),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    $false | (~spl10_13 | ~spl10_26)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f134,f202,f47])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl10_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f201])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    spl10_26 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl10_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl10_13 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    ~spl10_13 | ~spl10_30),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    $false | (~spl10_13 | ~spl10_30)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f134,f221,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl10_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    spl10_30 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl10_36),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    $false | spl10_36),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f32,f56,f29,f271,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X2,X1) | v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | spl10_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f269])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    spl10_36 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    ~spl10_36 | spl10_29 | ~spl10_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f265,f224,f216,f269])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    spl10_29 <=> v1_xboole_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl10_31 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | (spl10_29 | ~spl10_31)),
% 0.21/0.54    inference(backward_demodulation,[],[f218,f226])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl10_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f224])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0) | spl10_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f216])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    spl10_31 | ~spl10_8 | spl10_32 | spl10_33 | ~spl10_17 | spl10_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f255,f170,f155,f232,f228,f103,f224])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl10_8 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    spl10_32 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    spl10_33 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    spl10_17 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl10_20 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl10_20),
% 0.21/0.54    inference(superposition,[],[f172,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl10_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f170])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    spl10_31 | ~spl10_8 | spl10_32 | spl10_33 | ~spl10_16 | spl10_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f247,f174,f150,f232,f228,f103,f224])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    spl10_16 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl10_21 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl10_21),
% 0.21/0.54    inference(superposition,[],[f176,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f44])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl10_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f174])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    spl10_31 | ~spl10_8 | spl10_32 | spl10_33 | ~spl10_11 | spl10_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f195,f166,f121,f232,f228,f103,f224])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl10_11 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    spl10_19 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ~r2_hidden(k2_mcart_1(sK6),sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl10_19),
% 0.21/0.54    inference(superposition,[],[f168,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f50,f44])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl10_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f166])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    ~spl10_29 | spl10_30 | ~spl10_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f213,f91,f220,f216])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl10_6 <=> r1_tarski(sK3,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(sK0)) ) | ~spl10_6),
% 0.21/0.54    inference(resolution,[],[f95,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  % (26381)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK3)) ) | ~spl10_6),
% 0.21/0.54    inference(resolution,[],[f93,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    r1_tarski(sK3,sK0) | ~spl10_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f91])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    ~spl10_25 | spl10_26 | ~spl10_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f193,f83,f201,f197])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl10_25 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl10_5 <=> r1_tarski(sK4,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v1_xboole_0(sK1)) ) | ~spl10_5),
% 0.21/0.54    inference(resolution,[],[f87,f31])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK4)) ) | ~spl10_5),
% 0.21/0.54    inference(resolution,[],[f85,f39])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    r1_tarski(sK4,sK1) | ~spl10_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f83])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~spl10_19 | ~spl10_20 | ~spl10_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f23,f174,f170,f166])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl10_17 | ~spl10_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f142,f132,f155])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl10_13),
% 0.21/0.54    inference(resolution,[],[f134,f47])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl10_16 | ~spl10_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f141,f132,f150])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl10_13),
% 0.21/0.54    inference(resolution,[],[f134,f46])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl10_13 | ~spl10_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f117,f98,f132])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl10_7),
% 0.21/0.54    inference(resolution,[],[f100,f46])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl10_11 | ~spl10_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f118,f98,f121])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl10_7),
% 0.21/0.54    inference(resolution,[],[f100,f47])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~spl10_9 | spl10_10 | ~spl10_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f107,f75,f114,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl10_9 <=> v1_xboole_0(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl10_4 <=> r1_tarski(sK5,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK5) | ~v1_xboole_0(sK2)) ) | ~spl10_4),
% 0.21/0.54    inference(resolution,[],[f79,f31])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK5)) ) | ~spl10_4),
% 0.21/0.54    inference(resolution,[],[f77,f39])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    r1_tarski(sK5,sK2) | ~spl10_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl10_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f103])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.54    inference(definition_unfolding,[],[f24,f44])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl10_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f98])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f44])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl10_6 | ~spl10_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f89,f69,f91])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl10_3 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    r1_tarski(sK3,sK0) | ~spl10_3),
% 0.21/0.54    inference(resolution,[],[f71,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl10_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl10_5 | ~spl10_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f81,f64,f83])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl10_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    r1_tarski(sK4,sK1) | ~spl10_2),
% 0.21/0.54    inference(resolution,[],[f66,f43])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl10_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl10_4 | ~spl10_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f73,f59,f75])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl10_1 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    r1_tarski(sK5,sK2) | ~spl10_1),
% 0.21/0.54    inference(resolution,[],[f61,f43])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl10_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl10_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f69])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl10_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl10_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f59])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (26374)------------------------------
% 0.21/0.54  % (26374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26374)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (26374)Memory used [KB]: 11001
% 0.21/0.54  % (26374)Time elapsed: 0.116 s
% 0.21/0.54  % (26374)------------------------------
% 0.21/0.54  % (26374)------------------------------
% 0.21/0.54  % (26371)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (26361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (26357)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (26376)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (26364)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (26361)Refutation not found, incomplete strategy% (26361)------------------------------
% 0.21/0.55  % (26361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26350)Success in time 0.194 s
%------------------------------------------------------------------------------
