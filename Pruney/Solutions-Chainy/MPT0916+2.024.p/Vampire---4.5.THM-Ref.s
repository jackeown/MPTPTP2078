%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 295 expanded)
%              Number of leaves         :   38 ( 138 expanded)
%              Depth                    :    9
%              Number of atoms          :  524 (1229 expanded)
%              Number of equality atoms :   99 ( 171 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f70,f74,f78,f84,f90,f97,f103,f107,f120,f124,f142,f150,f158,f166,f169,f174,f178,f187,f194,f201,f212,f215,f219])).

fof(f219,plain,
    ( ~ spl7_12
    | spl7_17
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl7_12
    | spl7_17
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f217,f96])).

fof(f96,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_12
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f217,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl7_17
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f119,f141])).

fof(f141,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_22
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f119,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_17
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f215,plain,
    ( ~ spl7_13
    | spl7_16
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl7_13
    | spl7_16
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f213,f102])).

fof(f102,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_13
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f213,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl7_16
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f115,f186])).

fof(f186,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_28
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f115,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_16
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f212,plain,
    ( ~ spl7_6
    | ~ spl7_11
    | spl7_15
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_11
    | spl7_15
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f210,f89])).

fof(f89,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_11
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f210,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_6
    | spl7_15
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f111,f209])).

fof(f209,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_6
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f208,f128])).

fof(f128,plain,
    ( k1_xboole_0 != sK0
    | spl7_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f208,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_20
    | spl7_21
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f207,f132])).

fof(f132,plain,
    ( k1_xboole_0 != sK1
    | spl7_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f207,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_21
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f206,f136])).

fof(f136,plain,
    ( k1_xboole_0 != sK2
    | spl7_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f206,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(resolution,[],[f177,f65])).

fof(f65,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_6
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f177,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_27
  <=> ! [X1,X3,X0,X2] :
        ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f111,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_15
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f201,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f102,f199])).

fof(f199,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(resolution,[],[f157,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f157,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl7_24
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f194,plain,
    ( ~ spl7_11
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f89,f192])).

fof(f192,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(resolution,[],[f149,f106])).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f187,plain,
    ( spl7_28
    | ~ spl7_6
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f182,f172,f135,f131,f127,f63,f184])).

fof(f172,plain,
    ( spl7_26
  <=> ! [X1,X3,X0,X2] :
        ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f182,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_6
    | spl7_19
    | spl7_20
    | spl7_21
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f181,f128])).

fof(f181,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_20
    | spl7_21
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f180,f132])).

fof(f180,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_21
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f179,f136])).

fof(f179,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(resolution,[],[f173,f65])).

fof(f173,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f178,plain,(
    spl7_27 ),
    inference(avatar_split_clause,[],[f36,f176])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f174,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f35,f172])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f169,plain,
    ( ~ spl7_12
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f96,f167])).

fof(f167,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(resolution,[],[f165,f106])).

fof(f165,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl7_25
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f166,plain,
    ( spl7_25
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f161,f135,f53,f163])).

fof(f53,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f161,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f55,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f55,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f158,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f153,f131,f48,f155])).

fof(f48,plain,
    ( spl7_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f153,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f50,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f150,plain,
    ( spl7_23
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f145,f127,f43,f147])).

fof(f43,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(backward_demodulation,[],[f45,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f142,plain,
    ( spl7_19
    | spl7_20
    | spl7_21
    | spl7_22
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f125,f122,f63,f139,f135,f131,f127])).

fof(f122,plain,
    ( spl7_18
  <=> ! [X1,X3,X0,X2] :
        ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f125,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(resolution,[],[f123,f65])).

fof(f123,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f34,f122])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f120,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f23,f117,f113,f109])).

fof(f23,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
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
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f107,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f98,f76,f38,f105])).

fof(f38,plain,
    ( spl7_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f76,plain,
    ( spl7_9
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f103,plain,
    ( spl7_13
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f92,f81,f72,f100])).

fof(f72,plain,
    ( spl7_8
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f81,plain,
    ( spl7_10
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f92,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f73,f83])).

fof(f83,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k2_mcart_1(X0),X2) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f97,plain,
    ( spl7_12
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f91,f72,f58,f94])).

fof(f58,plain,
    ( spl7_5
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f91,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f90,plain,
    ( spl7_11
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f85,f81,f68,f87])).

fof(f68,plain,
    ( spl7_7
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_mcart_1(X0),X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f85,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(resolution,[],[f83,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k1_mcart_1(X0),X1) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f84,plain,
    ( spl7_10
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f79,f68,f58,f81])).

fof(f79,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(resolution,[],[f69,f60])).

fof(f78,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f74,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f70,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (1159)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.43  % (1159)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f221,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f70,f74,f78,f84,f90,f97,f103,f107,f120,f124,f142,f150,f158,f166,f169,f174,f178,f187,f194,f201,f212,f215,f219])).
% 0.22/0.43  fof(f219,plain,(
% 0.22/0.43    ~spl7_12 | spl7_17 | ~spl7_22),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f218])).
% 0.22/0.43  fof(f218,plain,(
% 0.22/0.43    $false | (~spl7_12 | spl7_17 | ~spl7_22)),
% 0.22/0.43    inference(subsumption_resolution,[],[f217,f96])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl7_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f94])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    spl7_12 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.43  fof(f217,plain,(
% 0.22/0.43    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl7_17 | ~spl7_22)),
% 0.22/0.43    inference(forward_demodulation,[],[f119,f141])).
% 0.22/0.43  fof(f141,plain,(
% 0.22/0.43    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl7_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f139])).
% 0.22/0.43  fof(f139,plain,(
% 0.22/0.43    spl7_22 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl7_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f117])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl7_17 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.43  fof(f215,plain,(
% 0.22/0.43    ~spl7_13 | spl7_16 | ~spl7_28),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.43  fof(f214,plain,(
% 0.22/0.43    $false | (~spl7_13 | spl7_16 | ~spl7_28)),
% 0.22/0.43    inference(subsumption_resolution,[],[f213,f102])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl7_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f100])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    spl7_13 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.43  fof(f213,plain,(
% 0.22/0.43    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl7_16 | ~spl7_28)),
% 0.22/0.43    inference(forward_demodulation,[],[f115,f186])).
% 0.22/0.43  fof(f186,plain,(
% 0.22/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl7_28),
% 0.22/0.43    inference(avatar_component_clause,[],[f184])).
% 0.22/0.43  fof(f184,plain,(
% 0.22/0.43    spl7_28 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.43  fof(f115,plain,(
% 0.22/0.43    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl7_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f113])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    spl7_16 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.43  fof(f212,plain,(
% 0.22/0.43    ~spl7_6 | ~spl7_11 | spl7_15 | spl7_19 | spl7_20 | spl7_21 | ~spl7_27),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.43  fof(f211,plain,(
% 0.22/0.43    $false | (~spl7_6 | ~spl7_11 | spl7_15 | spl7_19 | spl7_20 | spl7_21 | ~spl7_27)),
% 0.22/0.43    inference(subsumption_resolution,[],[f210,f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl7_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f87])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    spl7_11 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl7_6 | spl7_15 | spl7_19 | spl7_20 | spl7_21 | ~spl7_27)),
% 0.22/0.43    inference(backward_demodulation,[],[f111,f209])).
% 0.22/0.43  fof(f209,plain,(
% 0.22/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | (~spl7_6 | spl7_19 | spl7_20 | spl7_21 | ~spl7_27)),
% 0.22/0.43    inference(subsumption_resolution,[],[f208,f128])).
% 0.22/0.43  fof(f128,plain,(
% 0.22/0.43    k1_xboole_0 != sK0 | spl7_19),
% 0.22/0.43    inference(avatar_component_clause,[],[f127])).
% 0.22/0.43  fof(f127,plain,(
% 0.22/0.43    spl7_19 <=> k1_xboole_0 = sK0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.43  fof(f208,plain,(
% 0.22/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK0 | (~spl7_6 | spl7_20 | spl7_21 | ~spl7_27)),
% 0.22/0.43    inference(subsumption_resolution,[],[f207,f132])).
% 0.22/0.43  fof(f132,plain,(
% 0.22/0.43    k1_xboole_0 != sK1 | spl7_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f131])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    spl7_20 <=> k1_xboole_0 = sK1),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.43  fof(f207,plain,(
% 0.22/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | spl7_21 | ~spl7_27)),
% 0.22/0.43    inference(subsumption_resolution,[],[f206,f136])).
% 0.22/0.43  fof(f136,plain,(
% 0.22/0.43    k1_xboole_0 != sK2 | spl7_21),
% 0.22/0.43    inference(avatar_component_clause,[],[f135])).
% 0.22/0.43  fof(f135,plain,(
% 0.22/0.43    spl7_21 <=> k1_xboole_0 = sK2),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.43  fof(f206,plain,(
% 0.22/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_27)),
% 0.22/0.43    inference(resolution,[],[f177,f65])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl7_6 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.43  fof(f177,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_27),
% 0.22/0.43    inference(avatar_component_clause,[],[f176])).
% 0.22/0.43  fof(f176,plain,(
% 0.22/0.43    spl7_27 <=> ! [X1,X3,X0,X2] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl7_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f109])).
% 0.22/0.43  fof(f109,plain,(
% 0.22/0.43    spl7_15 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.43  fof(f201,plain,(
% 0.22/0.43    ~spl7_13 | ~spl7_14 | ~spl7_24),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.43  fof(f200,plain,(
% 0.22/0.43    $false | (~spl7_13 | ~spl7_14 | ~spl7_24)),
% 0.22/0.43    inference(subsumption_resolution,[],[f102,f199])).
% 0.22/0.43  fof(f199,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | (~spl7_14 | ~spl7_24)),
% 0.22/0.43    inference(resolution,[],[f157,f106])).
% 0.22/0.43  fof(f106,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl7_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f105])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    spl7_14 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.43  fof(f157,plain,(
% 0.22/0.43    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl7_24),
% 0.22/0.43    inference(avatar_component_clause,[],[f155])).
% 0.22/0.43  fof(f155,plain,(
% 0.22/0.43    spl7_24 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.43  fof(f194,plain,(
% 0.22/0.43    ~spl7_11 | ~spl7_14 | ~spl7_23),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.43  fof(f193,plain,(
% 0.22/0.43    $false | (~spl7_11 | ~spl7_14 | ~spl7_23)),
% 0.22/0.43    inference(subsumption_resolution,[],[f89,f192])).
% 0.22/0.43  fof(f192,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl7_14 | ~spl7_23)),
% 0.22/0.43    inference(resolution,[],[f149,f106])).
% 0.22/0.43  fof(f149,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_23),
% 0.22/0.43    inference(avatar_component_clause,[],[f147])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    spl7_23 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.43  fof(f187,plain,(
% 0.22/0.43    spl7_28 | ~spl7_6 | spl7_19 | spl7_20 | spl7_21 | ~spl7_26),
% 0.22/0.43    inference(avatar_split_clause,[],[f182,f172,f135,f131,f127,f63,f184])).
% 0.22/0.43  fof(f172,plain,(
% 0.22/0.43    spl7_26 <=> ! [X1,X3,X0,X2] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.43  fof(f182,plain,(
% 0.22/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (~spl7_6 | spl7_19 | spl7_20 | spl7_21 | ~spl7_26)),
% 0.22/0.43    inference(subsumption_resolution,[],[f181,f128])).
% 0.22/0.43  fof(f181,plain,(
% 0.22/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK0 | (~spl7_6 | spl7_20 | spl7_21 | ~spl7_26)),
% 0.22/0.43    inference(subsumption_resolution,[],[f180,f132])).
% 0.22/0.43  fof(f180,plain,(
% 0.22/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | spl7_21 | ~spl7_26)),
% 0.22/0.43    inference(subsumption_resolution,[],[f179,f136])).
% 0.22/0.43  fof(f179,plain,(
% 0.22/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_26)),
% 0.22/0.43    inference(resolution,[],[f173,f65])).
% 0.22/0.43  fof(f173,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_26),
% 0.22/0.43    inference(avatar_component_clause,[],[f172])).
% 0.22/0.43  fof(f178,plain,(
% 0.22/0.43    spl7_27),
% 0.22/0.43    inference(avatar_split_clause,[],[f36,f176])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(definition_unfolding,[],[f28,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.43  fof(f174,plain,(
% 0.22/0.43    spl7_26),
% 0.22/0.43    inference(avatar_split_clause,[],[f35,f172])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(definition_unfolding,[],[f29,f25])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f169,plain,(
% 0.22/0.43    ~spl7_12 | ~spl7_14 | ~spl7_25),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.43  fof(f168,plain,(
% 0.22/0.43    $false | (~spl7_12 | ~spl7_14 | ~spl7_25)),
% 0.22/0.43    inference(subsumption_resolution,[],[f96,f167])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,sK5)) ) | (~spl7_14 | ~spl7_25)),
% 0.22/0.43    inference(resolution,[],[f165,f106])).
% 0.22/0.43  fof(f165,plain,(
% 0.22/0.43    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl7_25),
% 0.22/0.43    inference(avatar_component_clause,[],[f163])).
% 0.22/0.43  fof(f163,plain,(
% 0.22/0.43    spl7_25 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    spl7_25 | ~spl7_4 | ~spl7_21),
% 0.22/0.43    inference(avatar_split_clause,[],[f161,f135,f53,f163])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl7_4 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.43  fof(f161,plain,(
% 0.22/0.43    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | (~spl7_4 | ~spl7_21)),
% 0.22/0.43    inference(backward_demodulation,[],[f55,f137])).
% 0.22/0.43  fof(f137,plain,(
% 0.22/0.43    k1_xboole_0 = sK2 | ~spl7_21),
% 0.22/0.43    inference(avatar_component_clause,[],[f135])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl7_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    spl7_24 | ~spl7_3 | ~spl7_20),
% 0.22/0.43    inference(avatar_split_clause,[],[f153,f131,f48,f155])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl7_3 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | (~spl7_3 | ~spl7_20)),
% 0.22/0.43    inference(backward_demodulation,[],[f50,f133])).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~spl7_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f131])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl7_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    spl7_23 | ~spl7_2 | ~spl7_19),
% 0.22/0.43    inference(avatar_split_clause,[],[f145,f127,f43,f147])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_19)),
% 0.22/0.43    inference(backward_demodulation,[],[f45,f129])).
% 0.22/0.43  fof(f129,plain,(
% 0.22/0.43    k1_xboole_0 = sK0 | ~spl7_19),
% 0.22/0.43    inference(avatar_component_clause,[],[f127])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f142,plain,(
% 0.22/0.43    spl7_19 | spl7_20 | spl7_21 | spl7_22 | ~spl7_6 | ~spl7_18),
% 0.22/0.43    inference(avatar_split_clause,[],[f125,f122,f63,f139,f135,f131,f127])).
% 0.22/0.43  fof(f122,plain,(
% 0.22/0.43    spl7_18 <=> ! [X1,X3,X0,X2] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.43  fof(f125,plain,(
% 0.22/0.43    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_18)),
% 0.22/0.43    inference(resolution,[],[f123,f65])).
% 0.22/0.43  fof(f123,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f122])).
% 0.22/0.43  fof(f124,plain,(
% 0.22/0.43    spl7_18),
% 0.22/0.43    inference(avatar_split_clause,[],[f34,f122])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(definition_unfolding,[],[f30,f25])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    ~spl7_15 | ~spl7_16 | ~spl7_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f117,f113,f109])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f16,f15,f14,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    spl7_14 | ~spl7_1 | ~spl7_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f98,f76,f38,f105])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl7_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    spl7_9 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl7_1 | ~spl7_9)),
% 0.22/0.43    inference(resolution,[],[f77,f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl7_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl7_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f76])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    spl7_13 | ~spl7_8 | ~spl7_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f92,f81,f72,f100])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl7_8 <=> ! [X1,X0,X2] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl7_10 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (~spl7_8 | ~spl7_10)),
% 0.22/0.43    inference(resolution,[],[f73,f83])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl7_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f81])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) ) | ~spl7_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f72])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    spl7_12 | ~spl7_5 | ~spl7_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f91,f72,f58,f94])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl7_5 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    r2_hidden(k2_mcart_1(sK6),sK5) | (~spl7_5 | ~spl7_8)),
% 0.22/0.43    inference(resolution,[],[f73,f60])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl7_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f58])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    spl7_11 | ~spl7_7 | ~spl7_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f85,f81,f68,f87])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl7_7 <=> ! [X1,X0,X2] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl7_7 | ~spl7_10)),
% 0.22/0.43    inference(resolution,[],[f83,f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) ) | ~spl7_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f68])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    spl7_10 | ~spl7_5 | ~spl7_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f79,f68,f58,f81])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | (~spl7_5 | ~spl7_7)),
% 0.22/0.43    inference(resolution,[],[f69,f60])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl7_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f76])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    spl7_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f72])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl7_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f68])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl7_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f33,f63])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.43    inference(definition_unfolding,[],[f21,f25])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl7_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f58])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.22/0.43    inference(definition_unfolding,[],[f22,f25])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl7_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f53])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl7_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f48])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl7_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f43])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl7_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f38])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (1159)------------------------------
% 0.22/0.43  % (1159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (1159)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (1159)Memory used [KB]: 6268
% 0.22/0.43  % (1159)Time elapsed: 0.010 s
% 0.22/0.43  % (1159)------------------------------
% 0.22/0.43  % (1159)------------------------------
% 0.22/0.43  % (1151)Success in time 0.071 s
%------------------------------------------------------------------------------
