%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 161 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :    6
%              Number of atoms          :  304 ( 464 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f66,f70,f74,f78,f82,f86,f104,f112,f118,f134,f138,f158,f162,f167,f199,f210,f224,f243,f248])).

fof(f248,plain,
    ( spl3_2
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_2
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_33 ),
    inference(unit_resulting_resolution,[],[f73,f65,f242,f157])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl3_33
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( ! [X0] : m1_subset_1(sK2(X0),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_6
  <=> ! [X0] : m1_subset_1(sK2(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f243,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f233,f165,f102,f59,f52,f241])).

fof(f52,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( spl3_13
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f165,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f233,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f232,f53])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f226,f103])).

fof(f103,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(superposition,[],[f166,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f224,plain,
    ( spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f73,f64,f209,f157])).

fof(f209,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_31
  <=> ! [X3,X4] : ~ r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f64,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_4
  <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f210,plain,
    ( spl3_31
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f206,f197,f102,f68,f208])).

fof(f68,plain,
    ( spl3_5
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f197,plain,
    ( spl3_30
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k3_subset_1(X0,X2),X1)
        | ~ r2_hidden(X2,k7_setfam_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f206,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f204,f69])).

fof(f69,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f204,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X4))) )
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(resolution,[],[f198,f103])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k3_subset_1(X0,X2),X1)
        | ~ r2_hidden(X2,k7_setfam_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl3_30
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f171,f165,f136,f132,f197])).

fof(f132,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f136,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k3_subset_1(X0,X2),X1)
        | ~ r2_hidden(X2,k7_setfam_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f170,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k3_subset_1(X0,X2),X1)
        | ~ r2_hidden(X2,k7_setfam_1(X0,X1))
        | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(superposition,[],[f166,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f167,plain,
    ( spl3_25
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f163,f160,f116,f165])).

fof(f116,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f160,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f161,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f39,f160])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f158,plain,
    ( spl3_23
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f114,f110,f76,f156])).

fof(f76,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(resolution,[],[f111,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f138,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f38,f136])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f134,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f37,f132])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f118,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f112,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f36,f110])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f104,plain,
    ( spl3_13
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f95,f84,f80,f102])).

fof(f80,plain,
    ( spl3_8
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f95,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f81,f85])).

fof(f85,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f81,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f82,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f74,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,
    ( ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f56,f63])).

fof(f50,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(f61,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f28,f59,f56])).

fof(f28,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (8384)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8391)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (8392)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8380)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8394)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (8400)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (8380)Refutation not found, incomplete strategy% (8380)------------------------------
% 0.21/0.52  % (8380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8380)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8380)Memory used [KB]: 10618
% 0.21/0.52  % (8380)Time elapsed: 0.083 s
% 0.21/0.52  % (8380)------------------------------
% 0.21/0.52  % (8380)------------------------------
% 0.21/0.52  % (8387)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (8400)Refutation not found, incomplete strategy% (8400)------------------------------
% 0.21/0.52  % (8400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8400)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8400)Memory used [KB]: 10618
% 0.21/0.52  % (8400)Time elapsed: 0.090 s
% 0.21/0.52  % (8400)------------------------------
% 0.21/0.52  % (8400)------------------------------
% 0.21/0.52  % (8399)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (8393)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (8383)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (8390)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (8390)Refutation not found, incomplete strategy% (8390)------------------------------
% 0.21/0.53  % (8390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8390)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8390)Memory used [KB]: 6012
% 0.21/0.53  % (8390)Time elapsed: 0.125 s
% 0.21/0.53  % (8390)------------------------------
% 0.21/0.53  % (8390)------------------------------
% 0.21/0.53  % (8382)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8381)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% 0.21/0.53  % (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8382)Memory used [KB]: 10618
% 0.21/0.53  % (8382)Time elapsed: 0.127 s
% 0.21/0.53  % (8382)------------------------------
% 0.21/0.53  % (8382)------------------------------
% 0.21/0.53  % (8385)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.54  % (8398)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (8389)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.54  % (8379)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8386)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.54  % (8389)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f54,f61,f66,f70,f74,f78,f82,f86,f104,f112,f118,f134,f138,f158,f162,f167,f199,f210,f224,f243,f248])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    spl3_2 | ~spl3_6 | ~spl3_23 | ~spl3_33),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    $false | (spl3_2 | ~spl3_6 | ~spl3_23 | ~spl3_33)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f73,f65,f242,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,X1) | k1_xboole_0 = X1) ) | ~spl3_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl3_23 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl3_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f241])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    spl3_33 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) ) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl3_6 <=> ! [X0] : m1_subset_1(sK2(X0),X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    spl3_33 | ~spl3_1 | ~spl3_3 | ~spl3_13 | ~spl3_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f233,f165,f102,f59,f52,f241])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl3_3 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl3_13 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_13 | ~spl3_25)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f52])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_3 | ~spl3_13 | ~spl3_25)),
% 0.21/0.54    inference(subsumption_resolution,[],[f226,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_3 | ~spl3_25)),
% 0.21/0.54    inference(superposition,[],[f166,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f165])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl3_4 | ~spl3_6 | ~spl3_23 | ~spl3_31),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f219])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    $false | (spl3_4 | ~spl3_6 | ~spl3_23 | ~spl3_31)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f73,f64,f209,f157])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))) ) | ~spl3_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    spl3_31 <=> ! [X3,X4] : ~r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl3_4 <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    spl3_31 | ~spl3_5 | ~spl3_13 | ~spl3_30),
% 0.21/0.54    inference(avatar_split_clause,[],[f206,f197,f102,f68,f208])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl3_5 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl3_30 <=> ! [X1,X0,X2] : (r2_hidden(k3_subset_1(X0,X2),X1) | ~r2_hidden(X2,k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0))) ) | (~spl3_5 | ~spl3_13 | ~spl3_30)),
% 0.21/0.54    inference(subsumption_resolution,[],[f204,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f68])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r2_hidden(X3,k7_setfam_1(X4,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X4)))) ) | (~spl3_13 | ~spl3_30)),
% 0.21/0.54    inference(resolution,[],[f198,f103])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),X1) | ~r2_hidden(X2,k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f197])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    spl3_30 | ~spl3_19 | ~spl3_20 | ~spl3_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f171,f165,f136,f132,f197])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl3_19 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl3_20 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),X1) | ~r2_hidden(X2,k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_19 | ~spl3_20 | ~spl3_25)),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),X1) | ~r2_hidden(X2,k7_setfam_1(X0,X1)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_19 | ~spl3_25)),
% 0.21/0.54    inference(superposition,[],[f166,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    spl3_25 | ~spl3_16 | ~spl3_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f163,f160,f116,f165])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl3_16 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl3_24 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) ) | (~spl3_16 | ~spl3_24)),
% 0.21/0.54    inference(subsumption_resolution,[],[f161,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl3_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) ) | ~spl3_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f160])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl3_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f160])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl3_23 | ~spl3_7 | ~spl3_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f110,f76,f156])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl3_7 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1) ) | (~spl3_7 | ~spl3_15)),
% 0.21/0.54    inference(resolution,[],[f111,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f76])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl3_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f110])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f136])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl3_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f132])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f116])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl3_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f110])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl3_13 | ~spl3_8 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f84,f80,f102])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl3_8 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl3_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(superposition,[],[f81,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f84])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f80])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f84])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f80])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f72])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ~spl3_4 | ~spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f56,f63])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.54    inference(inner_rewriting,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | k1_xboole_0 != k7_setfam_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl3_2 | spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f59,f56])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    k1_xboole_0 = k7_setfam_1(sK0,sK1) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f52])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8389)------------------------------
% 0.21/0.54  % (8389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8389)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8389)Memory used [KB]: 10746
% 0.21/0.54  % (8389)Time elapsed: 0.136 s
% 0.21/0.54  % (8389)------------------------------
% 0.21/0.54  % (8389)------------------------------
% 0.21/0.54  % (8378)Success in time 0.188 s
%------------------------------------------------------------------------------
