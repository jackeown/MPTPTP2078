%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t14_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 252 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :    7
%              Number of atoms          :  315 ( 563 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f107,f117,f124,f132,f141,f153,f162,f177,f186,f194,f206,f222,f232,f242,f263,f272,f281,f292,f304,f311,f368])).

fof(f368,plain,
    ( ~ spl5_2
    | spl5_17
    | ~ spl5_20
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_20
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f319,f212])).

fof(f212,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),k2_zfmisc_1(sK2,sK1))
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f185,f161,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t1_xboole_1)).

fof(f161,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_17
  <=> ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f185,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_20
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f319,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),k2_zfmisc_1(sK2,sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f221,f96,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t119_zfmisc_1)).

fof(f96,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f221,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_26
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f311,plain,
    ( spl5_42
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f233,f230,f175,f309])).

fof(f309,plain,
    ( spl5_42
  <=> r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f175,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f230,plain,
    ( spl5_28
  <=> v4_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f233,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(unit_resulting_resolution,[],[f176,f231,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',d18_relat_1)).

fof(f231,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f176,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f304,plain,
    ( spl5_40
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f293,f115,f302])).

fof(f302,plain,
    ( spl5_40
  <=> r1_relset_1(sK2,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f115,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f293,plain,
    ( r1_relset_1(sK2,sK0,sK3,sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f116,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_relset_1(X0,X1,X2,X2) ) ),
    inference(rectify,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',reflexivity_r1_relset_1)).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f292,plain,
    ( spl5_38
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f274,f270,f290])).

fof(f290,plain,
    ( spl5_38
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f270,plain,
    ( spl5_34
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f274,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(superposition,[],[f65,f271])).

fof(f271,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f270])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',existence_m1_subset_1)).

fof(f281,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f273,f270,f279])).

fof(f279,plain,
    ( spl5_36
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f273,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_34 ),
    inference(superposition,[],[f133,f271])).

fof(f133,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t3_subset)).

fof(f272,plain,
    ( spl5_34
    | ~ spl5_0
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f248,f240,f88,f270])).

fof(f88,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f240,plain,
    ( spl5_30
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f248,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_0
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f241,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_0 ),
    inference(backward_demodulation,[],[f98,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t6_boole)).

fof(f98,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f89,f64])).

fof(f89,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f88])).

fof(f241,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f240])).

fof(f263,plain,
    ( spl5_32
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f225,f220,f261])).

fof(f261,plain,
    ( spl5_32
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f225,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f221,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f242,plain,
    ( spl5_30
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f235,f88,f240])).

fof(f235,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f65,f234,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t2_subset)).

fof(f234,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f89,f65,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t5_subset)).

fof(f232,plain,
    ( spl5_28
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f199,f192,f230])).

fof(f192,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f199,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f193,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',cc2_relset_1)).

fof(f193,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f222,plain,
    ( spl5_26
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f215,f204,f175,f220])).

fof(f204,plain,
    ( spl5_24
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f215,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f176,f205,f66])).

fof(f205,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl5_24
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f198,f115,f204])).

fof(f198,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f116,f76])).

fof(f194,plain,
    ( spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f187,f184,f192])).

fof(f187,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f185,f72])).

fof(f186,plain,
    ( spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f178,f175,f184])).

fof(f178,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f176,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t21_relat_1)).

fof(f177,plain,
    ( spl5_18
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f170,f115,f175])).

fof(f170,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f116,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',cc1_relset_1)).

fof(f162,plain,
    ( ~ spl5_17
    | spl5_9 ),
    inference(avatar_split_clause,[],[f145,f122,f160])).

fof(f122,plain,
    ( spl5_9
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f145,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK1))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f123,f72])).

fof(f123,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f153,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f142,f95,f151])).

fof(f151,plain,
    ( spl5_14
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f142,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f96,f72])).

fof(f141,plain,
    ( spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f134,f115,f139])).

fof(f139,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f134,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f116,f71])).

fof(f132,plain,
    ( ~ spl5_11
    | spl5_9 ),
    inference(avatar_split_clause,[],[f125,f122,f130])).

fof(f130,plain,
    ( spl5_11
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f125,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f123,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t1_subset)).

fof(f124,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f61,f122])).

fof(f61,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & r1_tarski(k2_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & r1_tarski(k2_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',t14_relset_1)).

fof(f117,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f59,f115])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,
    ( spl5_4
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f98,f88,f105])).

fof(f105,plain,
    ( spl5_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f97,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f60,f95])).

fof(f60,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f62,f88])).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t14_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
