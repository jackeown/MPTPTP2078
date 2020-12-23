%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t62_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 239 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :  306 ( 678 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f84,f91,f98,f108,f119,f133,f154,f162,f180,f194,f207,f220,f239,f241,f250,f252])).

fof(f252,plain,
    ( ~ spl4_0
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f248,f62])).

fof(f62,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f248,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f187,f230])).

fof(f230,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f118,f219,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t5_subset)).

fof(f219,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_30
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f187,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_24
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f250,plain,
    ( ~ spl4_0
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f245,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f62,f219,f56])).

fof(f245,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f187,f118])).

fof(f241,plain,
    ( ~ spl4_14
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f203,f230])).

fof(f203,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f239,plain,
    ( ~ spl4_14
    | spl4_27
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_27
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f227,f193])).

fof(f193,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_27
  <=> ~ m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f227,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f118,f219,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t4_subset)).

fof(f220,plain,
    ( spl4_30
    | spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f209,f96,f82,f218])).

fof(f82,plain,
    ( spl4_7
  <=> ~ v3_setfam_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f209,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f83,f97,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',d13_setfam_1)).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f83,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f207,plain,
    ( ~ spl4_29
    | ~ spl4_0
    | spl4_25 ),
    inference(avatar_split_clause,[],[f200,f183,f61,f205])).

fof(f205,plain,
    ( spl4_29
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f183,plain,
    ( spl4_25
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f200,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_0
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f62,f184,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t8_boole)).

fof(f184,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f183])).

fof(f194,plain,
    ( spl4_24
    | ~ spl4_27
    | ~ spl4_0
    | spl4_23 ),
    inference(avatar_split_clause,[],[f181,f178,f61,f192,f186])).

fof(f178,plain,
    ( spl4_23
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f181,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | o_0_0_xboole_0 = sK1
    | ~ spl4_0
    | ~ spl4_23 ),
    inference(resolution,[],[f179,f124])).

fof(f124,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,X4)
        | ~ m1_subset_1(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl4_0 ),
    inference(resolution,[],[f49,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_0 ),
    inference(backward_demodulation,[],[f99,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t6_boole)).

fof(f99,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f62,f45])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t2_subset)).

fof(f179,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl4_23
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f172,f89,f68,f178])).

fof(f68,plain,
    ( spl4_2
  <=> v3_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f172,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f69,f90,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f69,plain,
    ( v3_setfam_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f162,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f155,f152,f160])).

fof(f160,plain,
    ( spl4_20
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f152,plain,
    ( spl4_18
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f155,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(superposition,[],[f46,f153])).

fof(f153,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',existence_m1_subset_1)).

fof(f154,plain,
    ( spl4_18
    | ~ spl4_0
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f139,f131,f61,f152])).

fof(f131,plain,
    ( spl4_16
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f139,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f132,f101])).

fof(f132,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl4_16
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f126,f61,f131])).

fof(f126,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f46,f125,f49])).

fof(f125,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f62,f46,f56])).

fof(f119,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f112,f75,f117])).

fof(f75,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t3_subset)).

fof(f76,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f108,plain,
    ( spl4_12
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f99,f61,f106])).

fof(f106,plain,
    ( spl4_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f98,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v3_setfam_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK0)
          & r1_tarski(X2,sK1)
          & v3_setfam_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ v3_setfam_1(sK2,X0)
        & r1_tarski(sK2,X1)
        & v3_setfam_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',t62_setfam_1)).

fof(f91,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f44,f61])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t62_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
