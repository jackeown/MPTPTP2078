%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 214 expanded)
%              Number of leaves         :   28 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 680 expanded)
%              Number of equality atoms :   88 ( 159 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f64,f68,f73,f81,f85,f89,f97,f102,f111,f119,f123,f129,f136,f148,f166,f171,f177,f182,f197,f202,f207,f211,f228])).

fof(f228,plain,
    ( ~ spl7_1
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f226,f101])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_13
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f226,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f52,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f224,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k1_setfam_1(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_8
  <=> k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f224,plain,
    ( sK0 = k1_setfam_1(k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f218,f96])).

fof(f96,plain,
    ( ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_12
  <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f218,plain,
    ( k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl7_17
    | ~ spl7_25
    | spl7_27
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f162,f214])).

fof(f214,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_17
    | spl7_27
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f213,f201])).

fof(f201,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_27
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f213,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_17
    | ~ spl7_28 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_17
    | ~ spl7_28 ),
    inference(resolution,[],[f210,f118])).

fof(f118,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,sK5(X0,X2))
        | k1_xboole_0 = X0
        | r2_hidden(X2,k1_setfam_1(X0)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_17
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X2,sK5(X0,X2))
        | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f210,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,sK5(sK2,X2))
        | r2_hidden(X2,k1_setfam_1(sK2)) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_28
  <=> ! [X2] :
        ( r2_hidden(sK1,sK5(sK2,X2))
        | r2_hidden(X2,k1_setfam_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f162,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_25
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f52,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f211,plain,
    ( spl7_26
    | spl7_28
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f205,f121,f71,f209,f164])).

fof(f164,plain,
    ( spl7_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f71,plain,
    ( spl7_6
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f121,plain,
    ( spl7_18
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK5(X0,X2),X0)
        | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f205,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,sK5(sK2,X2))
        | k1_xboole_0 = sK2
        | r2_hidden(X2,k1_setfam_1(sK2)) )
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(resolution,[],[f72,f122])).

fof(f122,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK5(X0,X2),X0)
        | k1_xboole_0 = X0
        | r2_hidden(X2,k1_setfam_1(X0)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f72,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(sK1,X3) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f207,plain,
    ( spl7_5
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f203,f71,f62,f66])).

fof(f66,plain,
    ( spl7_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f62,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f203,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f72,f63])).

fof(f63,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f202,plain,
    ( ~ spl7_27
    | spl7_3
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f198,f161,f59,f169])).

fof(f59,plain,
    ( spl7_3
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f198,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_3
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f60,f162])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f197,plain,
    ( spl7_26
    | spl7_6
    | ~ spl7_19
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f184,f169,f127,f71,f164])).

fof(f127,plain,
    ( spl7_19
  <=> ! [X3,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X3,X0)
        | r2_hidden(X2,X3)
        | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_19
    | ~ spl7_27 ),
    inference(resolution,[],[f170,f128])).

fof(f128,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(X2,k1_setfam_1(X0))
        | ~ r2_hidden(X3,X0)
        | r2_hidden(X2,X3)
        | k1_xboole_0 = X0 )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f170,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f182,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f180,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f179,f96])).

fof(f179,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_3
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f60,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f164])).

fof(f177,plain,
    ( ~ spl7_4
    | ~ spl7_13
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f173,f101])).

fof(f173,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(backward_demodulation,[],[f63,f165])).

fof(f171,plain,
    ( spl7_27
    | ~ spl7_3
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f167,f161,f59,f169])).

fof(f167,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_3
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f69,f162])).

fof(f69,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f166,plain,
    ( spl7_25
    | spl7_26
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f153,f146,f55,f164,f161])).

fof(f55,plain,
    ( spl7_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f146,plain,
    ( spl7_22
  <=> ! [X3,X2] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(resolution,[],[f147,f56])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f147,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | k1_xboole_0 = X3
        | k1_setfam_1(X3) = k8_setfam_1(X2,X3) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl7_22
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f140,f134,f109,f146])).

fof(f109,plain,
    ( spl7_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f134,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f140,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(superposition,[],[f135,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f34,f134])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f129,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f45,f127])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f123,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f44,f121])).

fof(f44,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f119,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f43,f117])).

fof(f43,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f111,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f32,f109])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f102,plain,
    ( spl7_13
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f98,f87,f83,f100])).

fof(f83,plain,
    ( spl7_9
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f87,plain,
    ( spl7_10
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f98,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(superposition,[],[f84,f88])).

fof(f88,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f84,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f97,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f49,f95])).

fof(f49,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

% (32255)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f85,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f23,f83])).

fof(f23,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f81,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f19,f71,f59])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(sK1,X3)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f68,plain,
    ( ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f18,f66,f59])).

fof(f18,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f17,f62,f59])).

fof(f17,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (32248)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (32246)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (32261)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (32250)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (32245)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (32265)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (32248)Refutation not found, incomplete strategy% (32248)------------------------------
% 0.22/0.50  % (32248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32248)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32248)Memory used [KB]: 10746
% 0.22/0.50  % (32248)Time elapsed: 0.079 s
% 0.22/0.50  % (32248)------------------------------
% 0.22/0.50  % (32248)------------------------------
% 0.22/0.50  % (32246)Refutation not found, incomplete strategy% (32246)------------------------------
% 0.22/0.50  % (32246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32246)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32246)Memory used [KB]: 10618
% 0.22/0.50  % (32246)Time elapsed: 0.070 s
% 0.22/0.50  % (32246)------------------------------
% 0.22/0.50  % (32246)------------------------------
% 0.22/0.50  % (32254)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (32265)Refutation not found, incomplete strategy% (32265)------------------------------
% 0.22/0.51  % (32265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32265)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32265)Memory used [KB]: 10618
% 0.22/0.51  % (32265)Time elapsed: 0.071 s
% 0.22/0.51  % (32265)------------------------------
% 0.22/0.51  % (32265)------------------------------
% 0.22/0.51  % (32262)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (32251)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (32254)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f53,f57,f64,f68,f73,f81,f85,f89,f97,f102,f111,f119,f123,f129,f136,f148,f166,f171,f177,f182,f197,f202,f207,f211,f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ~spl7_1 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    $false | (~spl7_1 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f226,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl7_13 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_xboole_0) | (~spl7_1 | ~spl7_8 | ~spl7_12 | ~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(backward_demodulation,[],[f52,f225])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (~spl7_8 | ~spl7_12 | ~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(forward_demodulation,[],[f224,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    k1_xboole_0 = k1_setfam_1(k1_xboole_0) | ~spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl7_8 <=> k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    sK0 = k1_setfam_1(k1_xboole_0) | (~spl7_12 | ~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(forward_demodulation,[],[f218,f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl7_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl7_12 <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0) | (~spl7_17 | ~spl7_25 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(backward_demodulation,[],[f162,f214])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | (~spl7_17 | spl7_27 | ~spl7_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f213,f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k1_setfam_1(sK2)) | spl7_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    spl7_27 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | (~spl7_17 | ~spl7_28)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl7_17 | ~spl7_28)),
% 0.22/0.51    inference(resolution,[],[f210,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r2_hidden(X2,sK5(X0,X2)) | k1_xboole_0 = X0 | r2_hidden(X2,k1_setfam_1(X0))) ) | ~spl7_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl7_17 <=> ! [X0,X2] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,k1_setfam_1(X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ( ! [X2] : (r2_hidden(sK1,sK5(sK2,X2)) | r2_hidden(X2,k1_setfam_1(sK2))) ) | ~spl7_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    spl7_28 <=> ! [X2] : (r2_hidden(sK1,sK5(sK2,X2)) | r2_hidden(X2,k1_setfam_1(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl7_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f161])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl7_25 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    r2_hidden(sK1,sK0) | ~spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl7_1 <=> r2_hidden(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl7_26 | spl7_28 | ~spl7_6 | ~spl7_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f205,f121,f71,f209,f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl7_26 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl7_6 <=> ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl7_18 <=> ! [X0,X2] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,k1_setfam_1(X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ( ! [X2] : (r2_hidden(sK1,sK5(sK2,X2)) | k1_xboole_0 = sK2 | r2_hidden(X2,k1_setfam_1(sK2))) ) | (~spl7_6 | ~spl7_18)),
% 0.22/0.51    inference(resolution,[],[f72,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),X0) | k1_xboole_0 = X0 | r2_hidden(X2,k1_setfam_1(X0))) ) | ~spl7_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3)) ) | ~spl7_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f71])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    spl7_5 | ~spl7_4 | ~spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f203,f71,f62,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    spl7_5 <=> r2_hidden(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl7_4 <=> r2_hidden(sK3,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3) | (~spl7_4 | ~spl7_6)),
% 0.22/0.51    inference(resolution,[],[f72,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    r2_hidden(sK3,sK2) | ~spl7_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ~spl7_27 | spl7_3 | ~spl7_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f198,f161,f59,f169])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl7_3 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k1_setfam_1(sK2)) | (spl7_3 | ~spl7_25)),
% 0.22/0.51    inference(forward_demodulation,[],[f60,f162])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl7_26 | spl7_6 | ~spl7_19 | ~spl7_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f169,f127,f71,f164])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl7_19 <=> ! [X3,X0,X2] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | (~spl7_19 | ~spl7_27)),
% 0.22/0.51    inference(resolution,[],[f170,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X2,k1_setfam_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | k1_xboole_0 = X0) ) | ~spl7_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f169])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~spl7_1 | spl7_3 | ~spl7_12 | ~spl7_26),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    $false | (~spl7_1 | spl7_3 | ~spl7_12 | ~spl7_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f52])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK0) | (spl7_3 | ~spl7_12 | ~spl7_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f179,f96])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_3 | ~spl7_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f60,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl7_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f164])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ~spl7_4 | ~spl7_13 | ~spl7_26),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    $false | (~spl7_4 | ~spl7_13 | ~spl7_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f101])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    r2_hidden(sK3,k1_xboole_0) | (~spl7_4 | ~spl7_26)),
% 0.22/0.51    inference(backward_demodulation,[],[f63,f165])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    spl7_27 | ~spl7_3 | ~spl7_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f167,f161,f59,f169])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl7_3 | ~spl7_25)),
% 0.22/0.51    inference(backward_demodulation,[],[f69,f162])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    spl7_25 | spl7_26 | ~spl7_2 | ~spl7_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f153,f146,f55,f164,f161])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl7_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl7_22 <=> ! [X3,X2] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl7_2 | ~spl7_22)),
% 0.22/0.51    inference(resolution,[],[f147,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) ) | ~spl7_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    spl7_22 | ~spl7_15 | ~spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f140,f134,f109,f146])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl7_15 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl7_20 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl7_15 | ~spl7_20)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl7_15 | ~spl7_20)),
% 0.22/0.51    inference(superposition,[],[f135,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl7_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl7_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f134])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f134])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl7_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f127])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl7_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f121])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl7_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f117])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl7_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f109])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl7_13 | ~spl7_9 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f98,f87,f83,f100])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl7_9 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl7_10 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl7_9 | ~spl7_10)),
% 0.22/0.51    inference(superposition,[],[f84,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl7_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl7_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f95])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f46,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  % (32255)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(equality_resolution,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f87])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f83])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl7_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f79])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.22/0.51    inference(equality_resolution,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 0.22/0.51    inference(equality_resolution,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl7_3 | spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f71,f59])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~spl7_3 | ~spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f66,f59])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~spl7_3 | spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f62,f59])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f55])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f51])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    r2_hidden(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (32254)------------------------------
% 0.22/0.51  % (32254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32254)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (32254)Memory used [KB]: 10746
% 0.22/0.51  % (32254)Time elapsed: 0.060 s
% 0.22/0.51  % (32254)------------------------------
% 0.22/0.51  % (32254)------------------------------
% 0.22/0.51  % (32244)Success in time 0.152 s
%------------------------------------------------------------------------------
