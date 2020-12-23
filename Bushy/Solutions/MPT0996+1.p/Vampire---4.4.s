%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t44_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:45 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 207 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  251 ( 437 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f80,f88,f97,f113,f124,f137,f145,f163,f168,f181,f186,f193,f209,f223,f231])).

fof(f231,plain,
    ( ~ spl5_4
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(resolution,[],[f228,f87])).

fof(f87,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_7
  <=> ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f228,plain,
    ( ! [X1] : r1_tarski(k7_relset_1(sK0,sK1,sK3,X1),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f225,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t3_subset)).

fof(f225,plain,
    ( ! [X3] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f57,f79])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',dt_k7_relset_1)).

fof(f223,plain,
    ( spl5_32
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f214,f201,f122,f111,f221])).

fof(f221,plain,
    ( spl5_32
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f111,plain,
    ( spl5_10
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f122,plain,
    ( spl5_12
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f201,plain,
    ( spl5_28
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f214,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f210,f123])).

fof(f123,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f210,plain,
    ( sK3 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_28 ),
    inference(resolution,[],[f202,f115])).

fof(f115,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK4(k1_zfmisc_1(o_0_0_xboole_0)) = X2 )
    | ~ spl5_10 ),
    inference(resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t8_boole)).

fof(f112,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f202,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f209,plain,
    ( spl5_28
    | spl5_30
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f195,f78,f207,f201])).

fof(f207,plain,
    ( spl5_30
  <=> m1_subset_1(sK4(sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f195,plain,
    ( m1_subset_1(sK4(sK3),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f117,f79])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',existence_m1_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t2_subset)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t4_subset)).

fof(f193,plain,
    ( ~ spl5_27
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f184,f173,f191])).

fof(f191,plain,
    ( spl5_27
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f173,plain,
    ( spl5_22
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f184,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3)
    | ~ spl5_22 ),
    inference(resolution,[],[f174,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',antisymmetry_r2_hidden)).

fof(f174,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f186,plain,
    ( ~ spl5_25
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f185,f173,f176])).

fof(f176,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f185,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22 ),
    inference(resolution,[],[f174,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t7_boole)).

fof(f181,plain,
    ( spl5_22
    | spl5_24
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f100,f78,f179,f173])).

fof(f179,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f100,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(resolution,[],[f51,f79])).

fof(f168,plain,
    ( ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f167,f161,f152])).

fof(f152,plain,
    ( spl5_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f161,plain,
    ( spl5_20
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f167,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_20 ),
    inference(resolution,[],[f162,f54])).

fof(f162,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl5_18
    | spl5_20
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f129,f122,f161,f155])).

fof(f155,plain,
    ( spl5_18
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f129,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(superposition,[],[f99,f123])).

fof(f145,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f130,f122,f143])).

fof(f143,plain,
    ( spl5_16
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f130,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(superposition,[],[f48,f123])).

fof(f137,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f127,f122,f135])).

fof(f135,plain,
    ( spl5_14
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f127,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_12 ),
    inference(superposition,[],[f89,f123])).

fof(f89,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f52,f48])).

fof(f124,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f116,f111,f122])).

fof(f116,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_10 ),
    inference(resolution,[],[f112,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',d2_xboole_0)).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t6_boole)).

fof(f113,plain,
    ( spl5_10
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f106,f64,f111])).

fof(f64,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f106,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f105,f99])).

fof(f105,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f104,f48])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f56,f65])).

fof(f65,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t5_subset)).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f90,f78,f95])).

fof(f95,plain,
    ( spl5_8
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f90,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f52,f79])).

fof(f88,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',t44_funct_2)).

fof(f80,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f71,plain,
    ( spl5_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f45,f64])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t44_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
