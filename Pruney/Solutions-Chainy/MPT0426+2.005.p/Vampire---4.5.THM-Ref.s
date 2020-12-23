%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 227 expanded)
%              Number of leaves         :   28 ( 101 expanded)
%              Depth                    :    7
%              Number of atoms          :  381 ( 691 expanded)
%              Number of equality atoms :   72 ( 132 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f61,f65,f70,f78,f82,f92,f97,f101,f109,f113,f120,f128,f140,f153,f158,f164,f169,f223,f232,f237,f243,f247,f252,f284])).

fof(f284,plain,
    ( ~ spl8_11
    | ~ spl8_15
    | spl8_23
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_15
    | spl8_23
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f266,f91])).

fof(f91,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_11
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f266,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_15
    | spl8_23
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(backward_demodulation,[],[f246,f258])).

fof(f258,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_15
    | spl8_23
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f257,f236])).

fof(f236,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_23
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f257,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_15
    | ~ spl8_33 ),
    inference(resolution,[],[f251,f108])).

fof(f108,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,sK5(X0,X2))
        | k1_xboole_0 = X0
        | r2_hidden(X2,k1_setfam_1(X0)) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_15
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X2,sK5(X0,X2))
        | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f251,plain,
    ( r2_hidden(sK1,sK5(sK2,sK1))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl8_33
  <=> r2_hidden(sK1,sK5(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f246,plain,
    ( r2_hidden(sK5(sK2,sK1),sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl8_32
  <=> r2_hidden(sK5(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f252,plain,
    ( spl8_33
    | ~ spl8_6
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f248,f245,f68,f250])).

fof(f68,plain,
    ( spl8_6
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f248,plain,
    ( r2_hidden(sK1,sK5(sK2,sK1))
    | ~ spl8_6
    | ~ spl8_32 ),
    inference(resolution,[],[f246,f69])).

fof(f69,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(sK1,X3) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f247,plain,
    ( spl8_21
    | spl8_32
    | ~ spl8_16
    | spl8_23 ),
    inference(avatar_split_clause,[],[f238,f151,f111,f245,f138])).

fof(f138,plain,
    ( spl8_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f111,plain,
    ( spl8_16
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK5(X0,X2),X0)
        | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f238,plain,
    ( r2_hidden(sK5(sK2,sK1),sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_16
    | spl8_23 ),
    inference(resolution,[],[f236,f112])).

fof(f112,plain,
    ( ! [X2,X0] :
        ( r2_hidden(X2,k1_setfam_1(X0))
        | r2_hidden(sK5(X0,X2),X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f243,plain,
    ( spl8_5
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f239,f68,f59,f63])).

fof(f63,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f59,plain,
    ( spl8_4
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f239,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f69,f60])).

fof(f60,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f237,plain,
    ( ~ spl8_23
    | spl8_3
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f233,f221,f56,f151])).

fof(f56,plain,
    ( spl8_3
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f221,plain,
    ( spl8_30
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f233,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl8_3
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f57,f222])).

fof(f222,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f221])).

fof(f57,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f232,plain,
    ( spl8_21
    | spl8_6
    | ~ spl8_17
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f170,f151,f118,f68,f138])).

fof(f118,plain,
    ( spl8_17
  <=> ! [X3,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X3,X0)
        | r2_hidden(X2,X3)
        | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl8_17
    | ~ spl8_23 ),
    inference(resolution,[],[f152,f119])).

fof(f119,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(X2,k1_setfam_1(X0))
        | ~ r2_hidden(X3,X0)
        | r2_hidden(X2,X3)
        | k1_xboole_0 = X0 )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f152,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f223,plain,
    ( spl8_30
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f194,f135,f99,f52,f221])).

fof(f52,plain,
    ( spl8_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f99,plain,
    ( spl8_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f135,plain,
    ( spl8_20
  <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f194,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f192,f53])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f192,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(superposition,[],[f136,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f136,plain,
    ( k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f169,plain,
    ( ~ spl8_1
    | spl8_3
    | ~ spl8_12
    | ~ spl8_21
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | ~ spl8_12
    | ~ spl8_21
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f167,f49])).

fof(f49,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f167,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl8_3
    | ~ spl8_12
    | ~ spl8_21
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f160,f165])).

fof(f165,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl8_12
    | ~ spl8_24 ),
    inference(resolution,[],[f163,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k8_setfam_1(X0,k1_xboole_0) = X0 )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_12
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f163,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f160,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl8_3
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f57,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f164,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f156,f138,f52,f162])).

fof(f156,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_2
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f53,f139])).

fof(f158,plain,
    ( ~ spl8_4
    | ~ spl8_11
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f155,f91])).

fof(f155,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f60,f139])).

fof(f153,plain,
    ( spl8_23
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f149,f135,f99,f56,f52,f151])).

fof(f149,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f66,f147])).

fof(f147,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(superposition,[],[f136,f100])).

fof(f66,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f140,plain,
    ( spl8_20
    | spl8_21
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f129,f126,f52,f138,f135])).

fof(f126,plain,
    ( spl8_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f129,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f127,f53])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f29,f126])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f120,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f42,f118])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f113,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f40,f107])).

fof(f40,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f27,f99])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f97,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,
    ( spl8_11
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f88,f80,f76,f90])).

fof(f76,plain,
    ( spl8_8
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f80,plain,
    ( spl8_9
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(condensation,[],[f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(superposition,[],[f81,f77])).

fof(f77,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f81,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f78,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f18,f76])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f70,plain,
    ( spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f15,f68,f56])).

fof(f15,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(sK1,X3)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f65,plain,
    ( ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f14,f63,f56])).

fof(f14,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f13,f59,f56])).

fof(f13,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f16,f52])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f17,f48])).

fof(f17,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28855)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (28847)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (28843)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (28845)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (28847)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (28853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (28851)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (28851)Refutation not found, incomplete strategy% (28851)------------------------------
% 0.21/0.52  % (28851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28851)Memory used [KB]: 1663
% 0.21/0.52  % (28851)Time elapsed: 0.079 s
% 0.21/0.52  % (28851)------------------------------
% 0.21/0.52  % (28851)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f50,f54,f61,f65,f70,f78,f82,f92,f97,f101,f109,f113,f120,f128,f140,f153,f158,f164,f169,f223,f232,f237,f243,f247,f252,f284])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ~spl8_11 | ~spl8_15 | spl8_23 | ~spl8_32 | ~spl8_33),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    $false | (~spl8_11 | ~spl8_15 | spl8_23 | ~spl8_32 | ~spl8_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f266,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl8_11 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0) | (~spl8_15 | spl8_23 | ~spl8_32 | ~spl8_33)),
% 0.21/0.52    inference(backward_demodulation,[],[f246,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | (~spl8_15 | spl8_23 | ~spl8_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f257,f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k1_setfam_1(sK2)) | spl8_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl8_23 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl8_15 | ~spl8_33)),
% 0.21/0.52    inference(resolution,[],[f251,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_hidden(X2,sK5(X0,X2)) | k1_xboole_0 = X0 | r2_hidden(X2,k1_setfam_1(X0))) ) | ~spl8_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl8_15 <=> ! [X0,X2] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,k1_setfam_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    r2_hidden(sK1,sK5(sK2,sK1)) | ~spl8_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f250])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl8_33 <=> r2_hidden(sK1,sK5(sK2,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    r2_hidden(sK5(sK2,sK1),sK2) | ~spl8_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    spl8_32 <=> r2_hidden(sK5(sK2,sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    spl8_33 | ~spl8_6 | ~spl8_32),
% 0.21/0.52    inference(avatar_split_clause,[],[f248,f245,f68,f250])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl8_6 <=> ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    r2_hidden(sK1,sK5(sK2,sK1)) | (~spl8_6 | ~spl8_32)),
% 0.21/0.52    inference(resolution,[],[f246,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3)) ) | ~spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl8_21 | spl8_32 | ~spl8_16 | spl8_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f238,f151,f111,f245,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl8_21 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl8_16 <=> ! [X0,X2] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,k1_setfam_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    r2_hidden(sK5(sK2,sK1),sK2) | k1_xboole_0 = sK2 | (~spl8_16 | spl8_23)),
% 0.21/0.52    inference(resolution,[],[f236,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X2,X0] : (r2_hidden(X2,k1_setfam_1(X0)) | r2_hidden(sK5(X0,X2),X0) | k1_xboole_0 = X0) ) | ~spl8_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    spl8_5 | ~spl8_4 | ~spl8_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f239,f68,f59,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl8_5 <=> r2_hidden(sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl8_4 <=> r2_hidden(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    r2_hidden(sK1,sK3) | (~spl8_4 | ~spl8_6)),
% 0.21/0.52    inference(resolution,[],[f69,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2) | ~spl8_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~spl8_23 | spl8_3 | ~spl8_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f233,f221,f56,f151])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl8_3 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl8_30 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k1_setfam_1(sK2)) | (spl8_3 | ~spl8_30)),
% 0.21/0.52    inference(forward_demodulation,[],[f57,f222])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl8_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f221])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    spl8_21 | spl8_6 | ~spl8_17 | ~spl8_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f170,f151,f118,f68,f138])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl8_17 <=> ! [X3,X0,X2] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | (~spl8_17 | ~spl8_23)),
% 0.21/0.52    inference(resolution,[],[f152,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r2_hidden(X2,k1_setfam_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | k1_xboole_0 = X0) ) | ~spl8_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl8_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    spl8_30 | ~spl8_2 | ~spl8_13 | ~spl8_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f194,f135,f99,f52,f221])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl8_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl8_13 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl8_20 <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl8_2 | ~spl8_13 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl8_13 | ~spl8_20)),
% 0.21/0.52    inference(superposition,[],[f136,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl8_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~spl8_1 | spl8_3 | ~spl8_12 | ~spl8_21 | ~spl8_24),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    $false | (~spl8_1 | spl8_3 | ~spl8_12 | ~spl8_21 | ~spl8_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0) | ~spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl8_1 <=> r2_hidden(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0) | (spl8_3 | ~spl8_12 | ~spl8_21 | ~spl8_24)),
% 0.21/0.52    inference(backward_demodulation,[],[f160,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    sK0 = k8_setfam_1(sK0,k1_xboole_0) | (~spl8_12 | ~spl8_24)),
% 0.21/0.52    inference(resolution,[],[f163,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl8_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl8_12 <=> ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl8_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl8_24 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl8_3 | ~spl8_21)),
% 0.21/0.52    inference(forward_demodulation,[],[f57,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl8_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl8_24 | ~spl8_2 | ~spl8_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f156,f138,f52,f162])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl8_2 | ~spl8_21)),
% 0.21/0.52    inference(backward_demodulation,[],[f53,f139])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~spl8_4 | ~spl8_11 | ~spl8_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    $false | (~spl8_4 | ~spl8_11 | ~spl8_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f155,f91])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    r2_hidden(sK3,k1_xboole_0) | (~spl8_4 | ~spl8_21)),
% 0.21/0.52    inference(backward_demodulation,[],[f60,f139])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl8_23 | ~spl8_2 | ~spl8_3 | ~spl8_13 | ~spl8_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f149,f135,f99,f56,f52,f151])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl8_2 | ~spl8_3 | ~spl8_13 | ~spl8_20)),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl8_2 | ~spl8_13 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f53])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl8_13 | ~spl8_20)),
% 0.21/0.52    inference(superposition,[],[f136,f100])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl8_20 | spl8_21 | ~spl8_2 | ~spl8_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f126,f52,f138,f135])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl8_18 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | (~spl8_2 | ~spl8_18)),
% 0.21/0.52    inference(resolution,[],[f127,f53])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) ) | ~spl8_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl8_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f126])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl8_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f118])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl8_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f111])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl8_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f107])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl8_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f99])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl8_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f95])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl8_11 | ~spl8_8 | ~spl8_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f88,f80,f76,f90])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl8_8 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl8_9 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_8 | ~spl8_9)),
% 0.21/0.52    inference(condensation,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) ) | (~spl8_8 | ~spl8_9)),
% 0.21/0.52    inference(superposition,[],[f81,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl8_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl8_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f80])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl8_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f76])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl8_3 | spl8_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f15,f68,f56])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~spl8_3 | ~spl8_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f14,f63,f56])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~spl8_3 | spl8_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f13,f59,f56])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f52])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f48])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28847)------------------------------
% 0.21/0.52  % (28847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28847)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28847)Memory used [KB]: 10746
% 0.21/0.52  % (28847)Time elapsed: 0.074 s
% 0.21/0.52  % (28847)------------------------------
% 0.21/0.52  % (28847)------------------------------
% 0.21/0.52  % (28837)Success in time 0.16 s
%------------------------------------------------------------------------------
