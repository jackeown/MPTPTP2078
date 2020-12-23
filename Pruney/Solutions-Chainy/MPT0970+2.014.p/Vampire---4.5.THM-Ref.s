%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:50 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 405 expanded)
%              Number of leaves         :   39 ( 174 expanded)
%              Depth                    :   10
%              Number of atoms          :  590 (1229 expanded)
%              Number of equality atoms :  102 ( 269 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f862,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f75,f80,f85,f102,f115,f120,f125,f137,f152,f162,f213,f222,f258,f275,f311,f317,f347,f354,f365,f372,f525,f533,f543,f551,f651,f719,f726,f759,f839,f861])).

fof(f861,plain,
    ( spl8_18
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_53 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | spl8_18
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f859,f274])).

fof(f274,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_22
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f859,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl8_18
    | ~ spl8_20
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f850,f266])).

fof(f266,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl8_18
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f212,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f212,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_18
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f850,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_53 ),
    inference(resolution,[],[f838,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f838,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl8_53
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f839,plain,
    ( spl8_53
    | ~ spl8_3
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f799,f219,f134,f77,f836])).

fof(f77,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f134,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f799,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_3
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f282,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f282,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl8_3
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f79,f221])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f759,plain,
    ( ~ spl8_33
    | spl8_47
    | ~ spl8_48 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl8_33
    | spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f755,f718])).

fof(f718,plain,
    ( ~ sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_47 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl8_47
  <=> sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f755,plain,
    ( sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_33
    | ~ spl8_48 ),
    inference(resolution,[],[f751,f725])).

fof(f725,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl8_48
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f751,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sP5(X0,k1_xboole_0) )
    | ~ spl8_33 ),
    inference(resolution,[],[f720,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f720,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k2_relat_1(k1_xboole_0))
        | ~ r2_hidden(X0,X1)
        | sP5(X0,k1_xboole_0) )
    | ~ spl8_33 ),
    inference(resolution,[],[f524,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f524,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0))
        | sP5(X1,k1_xboole_0) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl8_33
  <=> ! [X1] :
        ( sP5(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f726,plain,
    ( spl8_48
    | ~ spl8_11
    | ~ spl8_19
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f472,f362,f215,f134,f723])).

fof(f215,plain,
    ( spl8_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f362,plain,
    ( spl8_28
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f472,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_19
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f418,f136])).

fof(f418,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK1),sK1)
    | ~ spl8_19
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f363,f217])).

fof(f217,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f215])).

fof(f363,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f719,plain,
    ( ~ spl8_47
    | ~ spl8_11
    | ~ spl8_19
    | spl8_26 ),
    inference(avatar_split_clause,[],[f470,f344,f215,f134,f716])).

fof(f344,plain,
    ( spl8_26
  <=> sP5(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f470,plain,
    ( ~ sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_19
    | spl8_26 ),
    inference(backward_demodulation,[],[f414,f136])).

fof(f414,plain,
    ( ~ sP5(sK4(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_19
    | spl8_26 ),
    inference(backward_demodulation,[],[f345,f217])).

fof(f345,plain,
    ( ~ sP5(sK4(sK2,sK1),sK2)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f344])).

fof(f651,plain,
    ( spl8_32
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f228,f215,f99,f518])).

fof(f518,plain,
    ( spl8_32
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f99,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f228,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f101,f217])).

fof(f101,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f551,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_7
    | spl8_35 ),
    inference(subsumption_resolution,[],[f548,f114])).

fof(f114,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f548,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl8_5
    | spl8_35 ),
    inference(resolution,[],[f542,f104])).

fof(f104,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(sK2),X1)
        | ~ v5_relat_1(sK2,X1) )
    | ~ spl8_5 ),
    inference(resolution,[],[f101,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f542,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl8_35
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f543,plain,
    ( ~ spl8_35
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_26
    | spl8_28 ),
    inference(avatar_split_clause,[],[f378,f362,f344,f77,f63,f540])).

fof(f63,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f378,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_26
    | spl8_28 ),
    inference(subsumption_resolution,[],[f377,f346])).

fof(f346,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f344])).

fof(f377,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_1
    | ~ spl8_3
    | spl8_28 ),
    inference(resolution,[],[f367,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ sP5(X0,sK2) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f67,f86])).

fof(f86,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f65,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl8_28 ),
    inference(resolution,[],[f364,f40])).

fof(f364,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f533,plain,
    ( ~ spl8_28
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f532,f344,f314,f77,f63,f362])).

fof(f314,plain,
    ( spl8_24
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f532,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f527,f316])).

fof(f316,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f314])).

fof(f527,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_26 ),
    inference(resolution,[],[f93,f346])).

fof(f93,plain,
    ( ! [X3] :
        ( ~ sP5(sK4(sK2,X3),sK2)
        | ~ r2_hidden(sK4(sK2,X3),X3)
        | k2_relat_1(sK2) = X3 )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f70,f86])).

fof(f70,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(sK4(sK2,X3),sK2)
        | ~ r2_hidden(sK4(sK2,X3),X3)
        | k2_relat_1(sK2) = X3 )
    | ~ spl8_1 ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(sK4(X0,X1),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f525,plain,
    ( spl8_33
    | ~ spl8_32
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f479,f255,f518,f523])).

fof(f255,plain,
    ( spl8_21
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f479,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | sP5(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) )
    | ~ spl8_21 ),
    inference(resolution,[],[f257,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f257,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f255])).

fof(f372,plain,
    ( spl8_26
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24
    | spl8_28 ),
    inference(avatar_split_clause,[],[f368,f362,f314,f77,f63,f344])).

fof(f368,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24
    | spl8_28 ),
    inference(subsumption_resolution,[],[f366,f316])).

fof(f366,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | spl8_28 ),
    inference(resolution,[],[f364,f94])).

fof(f94,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),X2)
        | sP5(sK4(sK2,X2),sK2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f69,f86])).

fof(f69,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | sP5(sK4(sK2,X2),sK2)
        | r2_hidden(sK4(sK2,X2),X2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl8_1 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(sK4(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f365,plain,
    ( ~ spl8_28
    | spl8_27 ),
    inference(avatar_split_clause,[],[f355,f351,f362])).

fof(f351,plain,
    ( spl8_27
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f355,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_27 ),
    inference(resolution,[],[f353,f24])).

fof(f24,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f353,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f351])).

fof(f354,plain,
    ( spl8_26
    | ~ spl8_27
    | ~ spl8_15
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f349,f340,f173,f351,f344])).

fof(f173,plain,
    ( spl8_15
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f340,plain,
    ( spl8_25
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f349,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_15
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f348,f175])).

fof(f175,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f348,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl8_25 ),
    inference(superposition,[],[f56,f342])).

fof(f342,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f340])).

fof(f56,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f347,plain,
    ( spl8_25
    | spl8_26
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24 ),
    inference(avatar_split_clause,[],[f325,f314,f77,f63,f344,f340])).

fof(f325,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | spl8_24 ),
    inference(subsumption_resolution,[],[f324,f316])).

fof(f324,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f94,f25])).

fof(f25,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f317,plain,
    ( ~ spl8_24
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f128,f122,f82,f314])).

fof(f82,plain,
    ( spl8_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f122,plain,
    ( spl8_9
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f128,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_4
    | ~ spl8_9 ),
    inference(superposition,[],[f84,f124])).

fof(f124,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f84,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f311,plain,
    ( spl8_15
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f163,f130,f117,f173])).

fof(f117,plain,
    ( spl8_8
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f130,plain,
    ( spl8_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f163,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f119,f132])).

fof(f132,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f119,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f275,plain,
    ( spl8_22
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f262,f219,f149,f272])).

fof(f149,plain,
    ( spl8_12
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f262,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f151,f221])).

fof(f151,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f258,plain,
    ( spl8_21
    | ~ spl8_1
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f223,f215,f63,f255])).

fof(f223,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f65,f217])).

fof(f222,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f202,f159,f149,f219,f215])).

fof(f159,plain,
    ( spl8_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f194,f151])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_14 ),
    inference(resolution,[],[f161,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f213,plain,
    ( ~ spl8_18
    | spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f188,f134,f130,f210])).

fof(f188,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl8_10
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f131,f136])).

fof(f131,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f162,plain,
    ( spl8_14
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f141,f134,f77,f159])).

fof(f141,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f79,f136])).

fof(f152,plain,
    ( spl8_12
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f140,f134,f72,f149])).

fof(f72,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f140,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f74,f136])).

fof(f74,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f137,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f97,f77,f72,f134,f130])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f92,f74])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,
    ( spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f88,f77,f122])).

fof(f88,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f120,plain,
    ( spl8_8
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f87,f77,f117])).

fof(f87,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f90,f77,f112])).

fof(f90,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,
    ( spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f86,f77,f99])).

fof(f85,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f29,f82])).

fof(f29,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f77])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (9216)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (9221)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (9214)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (9215)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (9236)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (9228)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (9237)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (9218)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (9224)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (9229)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (9224)Refutation not found, incomplete strategy% (9224)------------------------------
% 0.21/0.51  % (9224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9224)Memory used [KB]: 10746
% 0.21/0.51  % (9224)Time elapsed: 0.113 s
% 0.21/0.51  % (9224)------------------------------
% 0.21/0.51  % (9224)------------------------------
% 1.24/0.52  % (9240)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.52  % (9226)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.52  % (9238)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.52  % (9217)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.52  % (9232)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.52  % (9234)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.52  % (9219)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.52  % (9231)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (9227)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.53  % (9220)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.53  % (9230)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.53  % (9231)Refutation not found, incomplete strategy% (9231)------------------------------
% 1.39/0.53  % (9231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (9231)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (9231)Memory used [KB]: 10746
% 1.39/0.53  % (9231)Time elapsed: 0.127 s
% 1.39/0.53  % (9231)------------------------------
% 1.39/0.53  % (9231)------------------------------
% 1.39/0.53  % (9241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.53  % (9235)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (9222)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.54  % (9233)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (9239)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.54  % (9243)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (9242)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.54  % (9223)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.54  % (9225)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.58  % (9234)Refutation found. Thanks to Tanya!
% 1.39/0.58  % SZS status Theorem for theBenchmark
% 1.39/0.59  % SZS output start Proof for theBenchmark
% 1.39/0.59  fof(f862,plain,(
% 1.39/0.59    $false),
% 1.39/0.59    inference(avatar_sat_refutation,[],[f66,f75,f80,f85,f102,f115,f120,f125,f137,f152,f162,f213,f222,f258,f275,f311,f317,f347,f354,f365,f372,f525,f533,f543,f551,f651,f719,f726,f759,f839,f861])).
% 1.39/0.59  fof(f861,plain,(
% 1.39/0.59    spl8_18 | ~spl8_20 | ~spl8_22 | ~spl8_53),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f860])).
% 1.39/0.59  fof(f860,plain,(
% 1.39/0.59    $false | (spl8_18 | ~spl8_20 | ~spl8_22 | ~spl8_53)),
% 1.39/0.59    inference(subsumption_resolution,[],[f859,f274])).
% 1.39/0.59  fof(f274,plain,(
% 1.39/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl8_22),
% 1.39/0.59    inference(avatar_component_clause,[],[f272])).
% 1.39/0.59  fof(f272,plain,(
% 1.39/0.59    spl8_22 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.39/0.59  fof(f859,plain,(
% 1.39/0.59    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (spl8_18 | ~spl8_20 | ~spl8_53)),
% 1.39/0.59    inference(subsumption_resolution,[],[f850,f266])).
% 1.39/0.59  fof(f266,plain,(
% 1.39/0.59    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl8_18 | ~spl8_20)),
% 1.39/0.59    inference(backward_demodulation,[],[f212,f221])).
% 1.39/0.59  fof(f221,plain,(
% 1.39/0.59    k1_xboole_0 = sK0 | ~spl8_20),
% 1.39/0.59    inference(avatar_component_clause,[],[f219])).
% 1.39/0.59  fof(f219,plain,(
% 1.39/0.59    spl8_20 <=> k1_xboole_0 = sK0),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.39/0.59  fof(f212,plain,(
% 1.39/0.59    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | spl8_18),
% 1.39/0.59    inference(avatar_component_clause,[],[f210])).
% 1.39/0.59  fof(f210,plain,(
% 1.39/0.59    spl8_18 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.39/0.59  fof(f850,plain,(
% 1.39/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl8_53),
% 1.39/0.59    inference(resolution,[],[f838,f57])).
% 1.39/0.59  fof(f57,plain,(
% 1.39/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.39/0.59    inference(equality_resolution,[],[f51])).
% 1.39/0.59  fof(f51,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f23])).
% 1.39/0.59  fof(f23,plain,(
% 1.39/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.59    inference(flattening,[],[f22])).
% 1.39/0.59  fof(f22,plain,(
% 1.39/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.59    inference(ennf_transformation,[],[f9])).
% 1.39/0.59  fof(f9,axiom,(
% 1.39/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.59  fof(f838,plain,(
% 1.39/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_53),
% 1.39/0.59    inference(avatar_component_clause,[],[f836])).
% 1.39/0.59  fof(f836,plain,(
% 1.39/0.59    spl8_53 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.39/0.59  fof(f839,plain,(
% 1.39/0.59    spl8_53 | ~spl8_3 | ~spl8_11 | ~spl8_20),
% 1.39/0.59    inference(avatar_split_clause,[],[f799,f219,f134,f77,f836])).
% 1.39/0.59  fof(f77,plain,(
% 1.39/0.59    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.39/0.59  fof(f134,plain,(
% 1.39/0.59    spl8_11 <=> k1_xboole_0 = sK1),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.39/0.59  fof(f799,plain,(
% 1.39/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_3 | ~spl8_11 | ~spl8_20)),
% 1.39/0.59    inference(forward_demodulation,[],[f282,f136])).
% 1.39/0.59  fof(f136,plain,(
% 1.39/0.59    k1_xboole_0 = sK1 | ~spl8_11),
% 1.39/0.59    inference(avatar_component_clause,[],[f134])).
% 1.39/0.59  fof(f282,plain,(
% 1.39/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl8_3 | ~spl8_20)),
% 1.39/0.59    inference(forward_demodulation,[],[f79,f221])).
% 1.39/0.59  fof(f79,plain,(
% 1.39/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 1.39/0.59    inference(avatar_component_clause,[],[f77])).
% 1.39/0.59  fof(f759,plain,(
% 1.39/0.59    ~spl8_33 | spl8_47 | ~spl8_48),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f758])).
% 1.39/0.59  fof(f758,plain,(
% 1.39/0.59    $false | (~spl8_33 | spl8_47 | ~spl8_48)),
% 1.39/0.59    inference(subsumption_resolution,[],[f755,f718])).
% 1.39/0.59  fof(f718,plain,(
% 1.39/0.59    ~sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_47),
% 1.39/0.59    inference(avatar_component_clause,[],[f716])).
% 1.39/0.59  fof(f716,plain,(
% 1.39/0.59    spl8_47 <=> sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.39/0.59  fof(f755,plain,(
% 1.39/0.59    sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl8_33 | ~spl8_48)),
% 1.39/0.59    inference(resolution,[],[f751,f725])).
% 1.39/0.59  fof(f725,plain,(
% 1.39/0.59    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl8_48),
% 1.39/0.59    inference(avatar_component_clause,[],[f723])).
% 1.39/0.59  fof(f723,plain,(
% 1.39/0.59    spl8_48 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.39/0.59  fof(f751,plain,(
% 1.39/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sP5(X0,k1_xboole_0)) ) | ~spl8_33),
% 1.39/0.59    inference(resolution,[],[f720,f30])).
% 1.39/0.59  fof(f30,plain,(
% 1.39/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f2])).
% 1.39/0.59  fof(f2,axiom,(
% 1.39/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.59  fof(f720,plain,(
% 1.39/0.59    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(k1_xboole_0)) | ~r2_hidden(X0,X1) | sP5(X0,k1_xboole_0)) ) | ~spl8_33),
% 1.39/0.59    inference(resolution,[],[f524,f40])).
% 1.39/0.59  fof(f40,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f17])).
% 1.39/0.59  fof(f17,plain,(
% 1.39/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.59    inference(ennf_transformation,[],[f1])).
% 1.39/0.59  fof(f1,axiom,(
% 1.39/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.59  fof(f524,plain,(
% 1.39/0.59    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0)) | sP5(X1,k1_xboole_0)) ) | ~spl8_33),
% 1.39/0.59    inference(avatar_component_clause,[],[f523])).
% 1.39/0.59  fof(f523,plain,(
% 1.39/0.59    spl8_33 <=> ! [X1] : (sP5(X1,k1_xboole_0) | ~r2_hidden(X1,k2_relat_1(k1_xboole_0)))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.39/0.59  fof(f726,plain,(
% 1.39/0.59    spl8_48 | ~spl8_11 | ~spl8_19 | ~spl8_28),
% 1.39/0.59    inference(avatar_split_clause,[],[f472,f362,f215,f134,f723])).
% 1.39/0.59  fof(f215,plain,(
% 1.39/0.59    spl8_19 <=> k1_xboole_0 = sK2),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.39/0.59  fof(f362,plain,(
% 1.39/0.59    spl8_28 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.39/0.59  fof(f472,plain,(
% 1.39/0.59    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl8_11 | ~spl8_19 | ~spl8_28)),
% 1.39/0.59    inference(backward_demodulation,[],[f418,f136])).
% 1.39/0.59  fof(f418,plain,(
% 1.39/0.59    r2_hidden(sK4(k1_xboole_0,sK1),sK1) | (~spl8_19 | ~spl8_28)),
% 1.39/0.59    inference(backward_demodulation,[],[f363,f217])).
% 1.39/0.59  fof(f217,plain,(
% 1.39/0.59    k1_xboole_0 = sK2 | ~spl8_19),
% 1.39/0.59    inference(avatar_component_clause,[],[f215])).
% 1.39/0.59  fof(f363,plain,(
% 1.39/0.59    r2_hidden(sK4(sK2,sK1),sK1) | ~spl8_28),
% 1.39/0.59    inference(avatar_component_clause,[],[f362])).
% 1.39/0.59  fof(f719,plain,(
% 1.39/0.59    ~spl8_47 | ~spl8_11 | ~spl8_19 | spl8_26),
% 1.39/0.59    inference(avatar_split_clause,[],[f470,f344,f215,f134,f716])).
% 1.39/0.59  fof(f344,plain,(
% 1.39/0.59    spl8_26 <=> sP5(sK4(sK2,sK1),sK2)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.39/0.59  fof(f470,plain,(
% 1.39/0.59    ~sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl8_11 | ~spl8_19 | spl8_26)),
% 1.39/0.59    inference(backward_demodulation,[],[f414,f136])).
% 1.39/0.59  fof(f414,plain,(
% 1.39/0.59    ~sP5(sK4(k1_xboole_0,sK1),k1_xboole_0) | (~spl8_19 | spl8_26)),
% 1.39/0.59    inference(backward_demodulation,[],[f345,f217])).
% 1.39/0.59  fof(f345,plain,(
% 1.39/0.59    ~sP5(sK4(sK2,sK1),sK2) | spl8_26),
% 1.39/0.59    inference(avatar_component_clause,[],[f344])).
% 1.39/0.59  fof(f651,plain,(
% 1.39/0.59    spl8_32 | ~spl8_5 | ~spl8_19),
% 1.39/0.59    inference(avatar_split_clause,[],[f228,f215,f99,f518])).
% 1.39/0.60  fof(f518,plain,(
% 1.39/0.60    spl8_32 <=> v1_relat_1(k1_xboole_0)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.39/0.60  fof(f99,plain,(
% 1.39/0.60    spl8_5 <=> v1_relat_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.39/0.60  fof(f228,plain,(
% 1.39/0.60    v1_relat_1(k1_xboole_0) | (~spl8_5 | ~spl8_19)),
% 1.39/0.60    inference(backward_demodulation,[],[f101,f217])).
% 1.39/0.60  fof(f101,plain,(
% 1.39/0.60    v1_relat_1(sK2) | ~spl8_5),
% 1.39/0.60    inference(avatar_component_clause,[],[f99])).
% 1.39/0.60  fof(f551,plain,(
% 1.39/0.60    ~spl8_5 | ~spl8_7 | spl8_35),
% 1.39/0.60    inference(avatar_contradiction_clause,[],[f550])).
% 1.39/0.60  fof(f550,plain,(
% 1.39/0.60    $false | (~spl8_5 | ~spl8_7 | spl8_35)),
% 1.39/0.60    inference(subsumption_resolution,[],[f548,f114])).
% 1.39/0.60  fof(f114,plain,(
% 1.39/0.60    v5_relat_1(sK2,sK1) | ~spl8_7),
% 1.39/0.60    inference(avatar_component_clause,[],[f112])).
% 1.39/0.60  fof(f112,plain,(
% 1.39/0.60    spl8_7 <=> v5_relat_1(sK2,sK1)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.39/0.60  fof(f548,plain,(
% 1.39/0.60    ~v5_relat_1(sK2,sK1) | (~spl8_5 | spl8_35)),
% 1.39/0.60    inference(resolution,[],[f542,f104])).
% 1.39/0.60  fof(f104,plain,(
% 1.39/0.60    ( ! [X1] : (r1_tarski(k2_relat_1(sK2),X1) | ~v5_relat_1(sK2,X1)) ) | ~spl8_5),
% 1.39/0.60    inference(resolution,[],[f101,f39])).
% 1.39/0.60  fof(f39,plain,(
% 1.39/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f16])).
% 1.39/0.60  fof(f16,plain,(
% 1.39/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.60    inference(ennf_transformation,[],[f3])).
% 1.39/0.60  fof(f3,axiom,(
% 1.39/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.39/0.60  fof(f542,plain,(
% 1.39/0.60    ~r1_tarski(k2_relat_1(sK2),sK1) | spl8_35),
% 1.39/0.60    inference(avatar_component_clause,[],[f540])).
% 1.39/0.60  fof(f540,plain,(
% 1.39/0.60    spl8_35 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.39/0.60  fof(f543,plain,(
% 1.39/0.60    ~spl8_35 | ~spl8_1 | ~spl8_3 | ~spl8_26 | spl8_28),
% 1.39/0.60    inference(avatar_split_clause,[],[f378,f362,f344,f77,f63,f540])).
% 1.39/0.60  fof(f63,plain,(
% 1.39/0.60    spl8_1 <=> v1_funct_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.39/0.60  fof(f378,plain,(
% 1.39/0.60    ~r1_tarski(k2_relat_1(sK2),sK1) | (~spl8_1 | ~spl8_3 | ~spl8_26 | spl8_28)),
% 1.39/0.60    inference(subsumption_resolution,[],[f377,f346])).
% 1.39/0.60  fof(f346,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | ~spl8_26),
% 1.39/0.60    inference(avatar_component_clause,[],[f344])).
% 1.39/0.60  fof(f377,plain,(
% 1.39/0.60    ~r1_tarski(k2_relat_1(sK2),sK1) | ~sP5(sK4(sK2,sK1),sK2) | (~spl8_1 | ~spl8_3 | spl8_28)),
% 1.39/0.60    inference(resolution,[],[f367,f96])).
% 1.39/0.60  fof(f96,plain,(
% 1.39/0.60    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~sP5(X0,sK2)) ) | (~spl8_1 | ~spl8_3)),
% 1.39/0.60    inference(subsumption_resolution,[],[f67,f86])).
% 1.39/0.60  fof(f86,plain,(
% 1.39/0.60    v1_relat_1(sK2) | ~spl8_3),
% 1.39/0.60    inference(resolution,[],[f79,f43])).
% 1.39/0.60  fof(f43,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f18])).
% 1.39/0.60  fof(f18,plain,(
% 1.39/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.60    inference(ennf_transformation,[],[f5])).
% 1.39/0.60  fof(f5,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.60  fof(f67,plain,(
% 1.39/0.60    ( ! [X0] : (~v1_relat_1(sK2) | ~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_1),
% 1.39/0.60    inference(resolution,[],[f65,f55])).
% 1.39/0.60  fof(f55,plain,(
% 1.39/0.60    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.39/0.60    inference(equality_resolution,[],[f34])).
% 1.39/0.60  fof(f34,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f15,plain,(
% 1.39/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.60    inference(flattening,[],[f14])).
% 1.39/0.60  fof(f14,plain,(
% 1.39/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.60    inference(ennf_transformation,[],[f4])).
% 1.39/0.60  fof(f4,axiom,(
% 1.39/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.39/0.60  fof(f65,plain,(
% 1.39/0.60    v1_funct_1(sK2) | ~spl8_1),
% 1.39/0.60    inference(avatar_component_clause,[],[f63])).
% 1.39/0.60  fof(f367,plain,(
% 1.39/0.60    ( ! [X0] : (~r2_hidden(sK4(sK2,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl8_28),
% 1.39/0.60    inference(resolution,[],[f364,f40])).
% 1.39/0.60  fof(f364,plain,(
% 1.39/0.60    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_28),
% 1.39/0.60    inference(avatar_component_clause,[],[f362])).
% 1.39/0.60  fof(f533,plain,(
% 1.39/0.60    ~spl8_28 | ~spl8_1 | ~spl8_3 | spl8_24 | ~spl8_26),
% 1.39/0.60    inference(avatar_split_clause,[],[f532,f344,f314,f77,f63,f362])).
% 1.39/0.60  fof(f314,plain,(
% 1.39/0.60    spl8_24 <=> sK1 = k2_relat_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.39/0.60  fof(f532,plain,(
% 1.39/0.60    ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_1 | ~spl8_3 | spl8_24 | ~spl8_26)),
% 1.39/0.60    inference(subsumption_resolution,[],[f527,f316])).
% 1.39/0.60  fof(f316,plain,(
% 1.39/0.60    sK1 != k2_relat_1(sK2) | spl8_24),
% 1.39/0.60    inference(avatar_component_clause,[],[f314])).
% 1.39/0.60  fof(f527,plain,(
% 1.39/0.60    ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl8_1 | ~spl8_3 | ~spl8_26)),
% 1.39/0.60    inference(resolution,[],[f93,f346])).
% 1.39/0.60  fof(f93,plain,(
% 1.39/0.60    ( ! [X3] : (~sP5(sK4(sK2,X3),sK2) | ~r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) ) | (~spl8_1 | ~spl8_3)),
% 1.39/0.60    inference(subsumption_resolution,[],[f70,f86])).
% 1.39/0.60  fof(f70,plain,(
% 1.39/0.60    ( ! [X3] : (~v1_relat_1(sK2) | ~sP5(sK4(sK2,X3),sK2) | ~r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) ) | ~spl8_1),
% 1.39/0.60    inference(resolution,[],[f65,f37])).
% 1.39/0.60  fof(f37,plain,(
% 1.39/0.60    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f525,plain,(
% 1.39/0.60    spl8_33 | ~spl8_32 | ~spl8_21),
% 1.39/0.60    inference(avatar_split_clause,[],[f479,f255,f518,f523])).
% 1.39/0.60  fof(f255,plain,(
% 1.39/0.60    spl8_21 <=> v1_funct_1(k1_xboole_0)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.39/0.60  fof(f479,plain,(
% 1.39/0.60    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | sP5(X1,k1_xboole_0) | ~r2_hidden(X1,k2_relat_1(k1_xboole_0))) ) | ~spl8_21),
% 1.39/0.60    inference(resolution,[],[f257,f54])).
% 1.39/0.60  fof(f54,plain,(
% 1.39/0.60    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.39/0.60    inference(equality_resolution,[],[f35])).
% 1.39/0.60  fof(f35,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f257,plain,(
% 1.39/0.60    v1_funct_1(k1_xboole_0) | ~spl8_21),
% 1.39/0.60    inference(avatar_component_clause,[],[f255])).
% 1.39/0.60  fof(f372,plain,(
% 1.39/0.60    spl8_26 | ~spl8_1 | ~spl8_3 | spl8_24 | spl8_28),
% 1.39/0.60    inference(avatar_split_clause,[],[f368,f362,f314,f77,f63,f344])).
% 1.39/0.60  fof(f368,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | (~spl8_1 | ~spl8_3 | spl8_24 | spl8_28)),
% 1.39/0.60    inference(subsumption_resolution,[],[f366,f316])).
% 1.39/0.60  fof(f366,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | (~spl8_1 | ~spl8_3 | spl8_28)),
% 1.39/0.60    inference(resolution,[],[f364,f94])).
% 1.39/0.60  fof(f94,plain,(
% 1.39/0.60    ( ! [X2] : (r2_hidden(sK4(sK2,X2),X2) | sP5(sK4(sK2,X2),sK2) | k2_relat_1(sK2) = X2) ) | (~spl8_1 | ~spl8_3)),
% 1.39/0.60    inference(subsumption_resolution,[],[f69,f86])).
% 1.39/0.60  fof(f69,plain,(
% 1.39/0.60    ( ! [X2] : (~v1_relat_1(sK2) | sP5(sK4(sK2,X2),sK2) | r2_hidden(sK4(sK2,X2),X2) | k2_relat_1(sK2) = X2) ) | ~spl8_1),
% 1.39/0.60    inference(resolution,[],[f65,f36])).
% 1.39/0.60  fof(f36,plain,(
% 1.39/0.60    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f365,plain,(
% 1.39/0.60    ~spl8_28 | spl8_27),
% 1.39/0.60    inference(avatar_split_clause,[],[f355,f351,f362])).
% 1.39/0.60  fof(f351,plain,(
% 1.39/0.60    spl8_27 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.39/0.60  fof(f355,plain,(
% 1.39/0.60    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_27),
% 1.39/0.60    inference(resolution,[],[f353,f24])).
% 1.39/0.60  fof(f24,plain,(
% 1.39/0.60    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  fof(f13,plain,(
% 1.39/0.60    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.60    inference(flattening,[],[f12])).
% 1.39/0.60  fof(f12,plain,(
% 1.39/0.60    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.60    inference(ennf_transformation,[],[f11])).
% 1.39/0.60  fof(f11,negated_conjecture,(
% 1.39/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.39/0.60    inference(negated_conjecture,[],[f10])).
% 1.39/0.60  fof(f10,conjecture,(
% 1.39/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.39/0.60  fof(f353,plain,(
% 1.39/0.60    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | spl8_27),
% 1.39/0.60    inference(avatar_component_clause,[],[f351])).
% 1.39/0.60  fof(f354,plain,(
% 1.39/0.60    spl8_26 | ~spl8_27 | ~spl8_15 | ~spl8_25),
% 1.39/0.60    inference(avatar_split_clause,[],[f349,f340,f173,f351,f344])).
% 1.39/0.60  fof(f173,plain,(
% 1.39/0.60    spl8_15 <=> sK0 = k1_relat_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.39/0.60  fof(f340,plain,(
% 1.39/0.60    spl8_25 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.39/0.60  fof(f349,plain,(
% 1.39/0.60    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | sP5(sK4(sK2,sK1),sK2) | (~spl8_15 | ~spl8_25)),
% 1.39/0.60    inference(forward_demodulation,[],[f348,f175])).
% 1.39/0.60  fof(f175,plain,(
% 1.39/0.60    sK0 = k1_relat_1(sK2) | ~spl8_15),
% 1.39/0.60    inference(avatar_component_clause,[],[f173])).
% 1.39/0.60  fof(f348,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~spl8_25),
% 1.39/0.60    inference(superposition,[],[f56,f342])).
% 1.39/0.60  fof(f342,plain,(
% 1.39/0.60    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_25),
% 1.39/0.60    inference(avatar_component_clause,[],[f340])).
% 1.39/0.60  fof(f56,plain,(
% 1.39/0.60    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.39/0.60    inference(equality_resolution,[],[f31])).
% 1.39/0.60  fof(f31,plain,(
% 1.39/0.60    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f347,plain,(
% 1.39/0.60    spl8_25 | spl8_26 | ~spl8_1 | ~spl8_3 | spl8_24),
% 1.39/0.60    inference(avatar_split_clause,[],[f325,f314,f77,f63,f344,f340])).
% 1.39/0.60  fof(f325,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_1 | ~spl8_3 | spl8_24)),
% 1.39/0.60    inference(subsumption_resolution,[],[f324,f316])).
% 1.39/0.60  fof(f324,plain,(
% 1.39/0.60    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_1 | ~spl8_3)),
% 1.39/0.60    inference(resolution,[],[f94,f25])).
% 1.39/0.60  fof(f25,plain,(
% 1.39/0.60    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  fof(f317,plain,(
% 1.39/0.60    ~spl8_24 | spl8_4 | ~spl8_9),
% 1.39/0.60    inference(avatar_split_clause,[],[f128,f122,f82,f314])).
% 1.39/0.60  fof(f82,plain,(
% 1.39/0.60    spl8_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.39/0.60  fof(f122,plain,(
% 1.39/0.60    spl8_9 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.39/0.60  fof(f128,plain,(
% 1.39/0.60    sK1 != k2_relat_1(sK2) | (spl8_4 | ~spl8_9)),
% 1.39/0.60    inference(superposition,[],[f84,f124])).
% 1.39/0.60  fof(f124,plain,(
% 1.39/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_9),
% 1.39/0.60    inference(avatar_component_clause,[],[f122])).
% 1.39/0.60  fof(f84,plain,(
% 1.39/0.60    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_4),
% 1.39/0.60    inference(avatar_component_clause,[],[f82])).
% 1.39/0.60  fof(f311,plain,(
% 1.39/0.60    spl8_15 | ~spl8_8 | ~spl8_10),
% 1.39/0.60    inference(avatar_split_clause,[],[f163,f130,f117,f173])).
% 1.39/0.60  fof(f117,plain,(
% 1.39/0.60    spl8_8 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.39/0.60  fof(f130,plain,(
% 1.39/0.60    spl8_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.39/0.60  fof(f163,plain,(
% 1.39/0.60    sK0 = k1_relat_1(sK2) | (~spl8_8 | ~spl8_10)),
% 1.39/0.60    inference(backward_demodulation,[],[f119,f132])).
% 1.39/0.60  fof(f132,plain,(
% 1.39/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_10),
% 1.39/0.60    inference(avatar_component_clause,[],[f130])).
% 1.39/0.60  fof(f119,plain,(
% 1.39/0.60    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl8_8),
% 1.39/0.60    inference(avatar_component_clause,[],[f117])).
% 1.39/0.60  fof(f275,plain,(
% 1.39/0.60    spl8_22 | ~spl8_12 | ~spl8_20),
% 1.39/0.60    inference(avatar_split_clause,[],[f262,f219,f149,f272])).
% 1.39/0.60  fof(f149,plain,(
% 1.39/0.60    spl8_12 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.39/0.60  fof(f262,plain,(
% 1.39/0.60    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl8_12 | ~spl8_20)),
% 1.39/0.60    inference(backward_demodulation,[],[f151,f221])).
% 1.39/0.60  fof(f151,plain,(
% 1.39/0.60    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_12),
% 1.39/0.60    inference(avatar_component_clause,[],[f149])).
% 1.39/0.60  fof(f258,plain,(
% 1.39/0.60    spl8_21 | ~spl8_1 | ~spl8_19),
% 1.39/0.60    inference(avatar_split_clause,[],[f223,f215,f63,f255])).
% 1.39/0.60  fof(f223,plain,(
% 1.39/0.60    v1_funct_1(k1_xboole_0) | (~spl8_1 | ~spl8_19)),
% 1.39/0.60    inference(backward_demodulation,[],[f65,f217])).
% 1.39/0.60  fof(f222,plain,(
% 1.39/0.60    spl8_19 | spl8_20 | ~spl8_12 | ~spl8_14),
% 1.39/0.60    inference(avatar_split_clause,[],[f202,f159,f149,f219,f215])).
% 1.39/0.60  fof(f159,plain,(
% 1.39/0.60    spl8_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.39/0.60  fof(f202,plain,(
% 1.39/0.60    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl8_12 | ~spl8_14)),
% 1.39/0.60    inference(subsumption_resolution,[],[f194,f151])).
% 1.39/0.60  fof(f194,plain,(
% 1.39/0.60    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_14),
% 1.39/0.60    inference(resolution,[],[f161,f59])).
% 1.39/0.60  fof(f59,plain,(
% 1.39/0.60    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.39/0.60    inference(equality_resolution,[],[f49])).
% 1.39/0.60  fof(f49,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f23])).
% 1.39/0.60  fof(f161,plain,(
% 1.39/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_14),
% 1.39/0.60    inference(avatar_component_clause,[],[f159])).
% 1.39/0.60  fof(f213,plain,(
% 1.39/0.60    ~spl8_18 | spl8_10 | ~spl8_11),
% 1.39/0.60    inference(avatar_split_clause,[],[f188,f134,f130,f210])).
% 1.39/0.60  fof(f188,plain,(
% 1.39/0.60    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl8_10 | ~spl8_11)),
% 1.39/0.60    inference(forward_demodulation,[],[f131,f136])).
% 1.39/0.60  fof(f131,plain,(
% 1.39/0.60    sK0 != k1_relset_1(sK0,sK1,sK2) | spl8_10),
% 1.39/0.60    inference(avatar_component_clause,[],[f130])).
% 1.39/0.60  fof(f162,plain,(
% 1.39/0.60    spl8_14 | ~spl8_3 | ~spl8_11),
% 1.39/0.60    inference(avatar_split_clause,[],[f141,f134,f77,f159])).
% 1.39/0.60  fof(f141,plain,(
% 1.39/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_3 | ~spl8_11)),
% 1.39/0.60    inference(backward_demodulation,[],[f79,f136])).
% 1.39/0.60  fof(f152,plain,(
% 1.39/0.60    spl8_12 | ~spl8_2 | ~spl8_11),
% 1.39/0.60    inference(avatar_split_clause,[],[f140,f134,f72,f149])).
% 1.39/0.60  fof(f72,plain,(
% 1.39/0.60    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.39/0.60  fof(f140,plain,(
% 1.39/0.60    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl8_2 | ~spl8_11)),
% 1.39/0.60    inference(backward_demodulation,[],[f74,f136])).
% 1.39/0.60  fof(f74,plain,(
% 1.39/0.60    v1_funct_2(sK2,sK0,sK1) | ~spl8_2),
% 1.39/0.60    inference(avatar_component_clause,[],[f72])).
% 1.39/0.60  fof(f137,plain,(
% 1.39/0.60    spl8_10 | spl8_11 | ~spl8_2 | ~spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f97,f77,f72,f134,f130])).
% 1.39/0.60  fof(f97,plain,(
% 1.39/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl8_2 | ~spl8_3)),
% 1.39/0.60    inference(subsumption_resolution,[],[f92,f74])).
% 1.39/0.60  fof(f92,plain,(
% 1.39/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl8_3),
% 1.39/0.60    inference(resolution,[],[f79,f53])).
% 1.39/0.60  fof(f53,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f23])).
% 1.39/0.60  fof(f125,plain,(
% 1.39/0.60    spl8_9 | ~spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f88,f77,f122])).
% 1.39/0.60  fof(f88,plain,(
% 1.39/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_3),
% 1.39/0.60    inference(resolution,[],[f79,f45])).
% 1.39/0.60  fof(f45,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f20])).
% 1.39/0.60  fof(f20,plain,(
% 1.39/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.60    inference(ennf_transformation,[],[f8])).
% 1.39/0.60  fof(f8,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.39/0.60  fof(f120,plain,(
% 1.39/0.60    spl8_8 | ~spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f87,f77,f117])).
% 1.39/0.60  fof(f87,plain,(
% 1.39/0.60    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl8_3),
% 1.39/0.60    inference(resolution,[],[f79,f44])).
% 1.39/0.60  fof(f44,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f19])).
% 1.39/0.60  fof(f19,plain,(
% 1.39/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.60    inference(ennf_transformation,[],[f7])).
% 1.39/0.60  fof(f7,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.60  fof(f115,plain,(
% 1.39/0.60    spl8_7 | ~spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f90,f77,f112])).
% 1.39/0.60  fof(f90,plain,(
% 1.39/0.60    v5_relat_1(sK2,sK1) | ~spl8_3),
% 1.39/0.60    inference(resolution,[],[f79,f47])).
% 1.39/0.60  fof(f47,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f21])).
% 1.39/0.60  fof(f21,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.60    inference(ennf_transformation,[],[f6])).
% 1.39/0.60  fof(f6,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.60  fof(f102,plain,(
% 1.39/0.60    spl8_5 | ~spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f86,f77,f99])).
% 1.39/0.60  fof(f85,plain,(
% 1.39/0.60    ~spl8_4),
% 1.39/0.60    inference(avatar_split_clause,[],[f29,f82])).
% 1.39/0.60  fof(f29,plain,(
% 1.39/0.60    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  fof(f80,plain,(
% 1.39/0.60    spl8_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f28,f77])).
% 1.39/0.60  fof(f28,plain,(
% 1.39/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  fof(f75,plain,(
% 1.39/0.60    spl8_2),
% 1.39/0.60    inference(avatar_split_clause,[],[f27,f72])).
% 1.39/0.60  fof(f27,plain,(
% 1.39/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  fof(f66,plain,(
% 1.39/0.60    spl8_1),
% 1.39/0.60    inference(avatar_split_clause,[],[f26,f63])).
% 1.39/0.60  fof(f26,plain,(
% 1.39/0.60    v1_funct_1(sK2)),
% 1.39/0.60    inference(cnf_transformation,[],[f13])).
% 1.39/0.60  % SZS output end Proof for theBenchmark
% 1.39/0.60  % (9234)------------------------------
% 1.39/0.60  % (9234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.60  % (9234)Termination reason: Refutation
% 1.39/0.60  
% 1.39/0.60  % (9234)Memory used [KB]: 11257
% 1.39/0.60  % (9234)Time elapsed: 0.175 s
% 1.39/0.60  % (9234)------------------------------
% 1.39/0.60  % (9234)------------------------------
% 1.39/0.60  % (9213)Success in time 0.243 s
%------------------------------------------------------------------------------
