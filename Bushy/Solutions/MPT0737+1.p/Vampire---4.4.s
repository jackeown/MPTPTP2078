%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t25_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 261 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  326 ( 686 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f89,f96,f103,f113,f123,f130,f142,f153,f160,f174,f183,f190,f201,f241,f266,f295,f300,f302,f306])).

fof(f306,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_19
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f304,f88])).

fof(f88,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f304,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f303,f81])).

fof(f81,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_0
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f303,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f298,f283])).

fof(f283,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f88,f159,f81,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',redefinition_r1_ordinal1)).

fof(f159,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_19
  <=> ~ r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f298,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_33 ),
    inference(resolution,[],[f294,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',connectedness_r1_ordinal1)).

fof(f294,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl3_33
  <=> ~ r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f302,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_19
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f296,f283])).

fof(f296,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_33 ),
    inference(unit_resulting_resolution,[],[f81,f88,f294,f63])).

fof(f300,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_19
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f297,f283])).

fof(f297,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_33 ),
    inference(unit_resulting_resolution,[],[f88,f81,f294,f63])).

fof(f295,plain,
    ( ~ spl3_33
    | ~ spl3_0
    | ~ spl3_2
    | spl3_17 ),
    inference(avatar_split_clause,[],[f285,f151,f87,f80,f293])).

fof(f151,plain,
    ( spl3_17
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f285,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f81,f152,f88,f64])).

fof(f152,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f266,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f248,f239,f94,f264])).

fof(f264,plain,
    ( spl3_30
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f94,plain,
    ( spl3_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f239,plain,
    ( spl3_28
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f248,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f240,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f104,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t6_boole)).

fof(f104,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f95,f55])).

fof(f95,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f240,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl3_28
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f234,f94,f239])).

fof(f234,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f224,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t2_subset)).

fof(f224,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f95,f56,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t5_subset)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',existence_m1_subset_1)).

fof(f201,plain,
    ( ~ spl3_27
    | spl3_23 ),
    inference(avatar_split_clause,[],[f193,f181,f199])).

fof(f199,plain,
    ( spl3_27
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f181,plain,
    ( spl3_23
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f193,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f182,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t1_subset)).

fof(f182,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f190,plain,
    ( ~ spl3_25
    | spl3_21 ),
    inference(avatar_split_clause,[],[f175,f172,f188])).

fof(f188,plain,
    ( spl3_25
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f172,plain,
    ( spl3_21
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f175,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f173,f59])).

fof(f173,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f183,plain,
    ( ~ spl3_23
    | spl3_19 ),
    inference(avatar_split_clause,[],[f164,f158,f181])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f159,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t3_subset)).

fof(f174,plain,
    ( ~ spl3_21
    | spl3_17 ),
    inference(avatar_split_clause,[],[f163,f151,f172])).

fof(f163,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f152,f69])).

fof(f160,plain,
    ( ~ spl3_19
    | spl3_15 ),
    inference(avatar_split_clause,[],[f144,f140,f158])).

fof(f140,plain,
    ( spl3_15
  <=> ~ r3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f141,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',d9_xboole_0)).

fof(f141,plain,
    ( ~ r3_xboole_0(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f153,plain,
    ( ~ spl3_17
    | spl3_7 ),
    inference(avatar_split_clause,[],[f143,f101,f151])).

fof(f101,plain,
    ( spl3_7
  <=> ~ r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f143,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f67])).

fof(f102,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f142,plain,
    ( ~ spl3_15
    | spl3_7 ),
    inference(avatar_split_clause,[],[f134,f101,f140])).

fof(f134,plain,
    ( ~ r3_xboole_0(sK1,sK0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => r3_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',symmetry_r3_xboole_0)).

fof(f130,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f116,f87,f128])).

fof(f128,plain,
    ( spl3_12
  <=> r1_ordinal1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f116,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(condensation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',reflexivity_r1_ordinal1)).

fof(f123,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f115,f80,f121])).

fof(f121,plain,
    ( spl3_10
  <=> r1_ordinal1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f115,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f81,f75])).

fof(f113,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f104,f94,f111])).

fof(f111,plain,
    ( spl3_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f103,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r3_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r3_xboole_0(X0,sK1)
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => r3_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t25_ordinal1)).

fof(f96,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',dt_o_0_0_xboole_0)).

fof(f89,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
