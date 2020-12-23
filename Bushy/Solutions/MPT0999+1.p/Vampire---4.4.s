%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t47_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:46 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 205 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  246 ( 427 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f79,f87,f96,f112,f123,f136,f144,f162,f167,f180,f185,f192,f208,f222,f230])).

fof(f230,plain,
    ( ~ spl5_4
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(resolution,[],[f227,f86])).

fof(f86,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_7
  <=> ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f227,plain,
    ( ! [X1] : r1_tarski(k8_relset_1(sK0,sK1,sK3,X1),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f224,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t3_subset)).

fof(f224,plain,
    ( ! [X3] : m1_subset_1(k8_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',dt_k8_relset_1)).

fof(f222,plain,
    ( spl5_32
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f213,f200,f121,f110,f220])).

fof(f220,plain,
    ( spl5_32
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f110,plain,
    ( spl5_10
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f121,plain,
    ( spl5_12
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f200,plain,
    ( spl5_28
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f213,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f209,f122])).

fof(f122,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f209,plain,
    ( sK3 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_28 ),
    inference(resolution,[],[f201,f114])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK4(k1_zfmisc_1(o_0_0_xboole_0)) = X2 )
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t8_boole)).

fof(f111,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f201,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f200])).

fof(f208,plain,
    ( spl5_28
    | spl5_30
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f194,f77,f206,f200])).

fof(f206,plain,
    ( spl5_30
  <=> m1_subset_1(sK4(sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f194,plain,
    ( m1_subset_1(sK4(sK3),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f116,f78])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f54,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',existence_m1_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t2_subset)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t4_subset)).

fof(f192,plain,
    ( ~ spl5_27
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f183,f172,f190])).

fof(f190,plain,
    ( spl5_27
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f172,plain,
    ( spl5_22
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f183,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3)
    | ~ spl5_22 ),
    inference(resolution,[],[f173,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',antisymmetry_r2_hidden)).

fof(f173,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f185,plain,
    ( ~ spl5_25
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f184,f172,f175])).

fof(f175,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f184,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22 ),
    inference(resolution,[],[f173,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t7_boole)).

fof(f180,plain,
    ( spl5_22
    | spl5_24
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f99,f77,f178,f172])).

fof(f178,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f99,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(resolution,[],[f50,f78])).

fof(f167,plain,
    ( ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f166,f160,f151])).

fof(f151,plain,
    ( spl5_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f160,plain,
    ( spl5_20
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f166,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_20 ),
    inference(resolution,[],[f161,f53])).

fof(f161,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl5_18
    | spl5_20
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f128,f121,f160,f154])).

fof(f154,plain,
    ( spl5_18
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f128,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(superposition,[],[f98,f122])).

fof(f144,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f129,f121,f142])).

fof(f142,plain,
    ( spl5_16
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f129,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_12 ),
    inference(superposition,[],[f47,f122])).

fof(f136,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f126,f121,f134])).

fof(f134,plain,
    ( spl5_14
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f126,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_12 ),
    inference(superposition,[],[f88,f122])).

fof(f88,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f51,f47])).

fof(f123,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f115,f110,f121])).

fof(f115,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',d2_xboole_0)).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t6_boole)).

fof(f112,plain,
    ( spl5_10
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f105,f63,f110])).

fof(f63,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f105,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f104,f98])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f103,f47])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f55,f64])).

fof(f64,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t5_subset)).

fof(f96,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f89,f77,f94])).

fof(f94,plain,
    ( spl5_8
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f89,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f51,f78])).

fof(f87,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK3,sK2),sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',t47_funct_2)).

fof(f79,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f45,f70])).

fof(f70,plain,
    ( spl5_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f44,f63])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t47_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
