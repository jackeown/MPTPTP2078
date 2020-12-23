%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t176_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 268 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  326 ( 691 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f97,f104,f114,f124,f136,f147,f154,f171,f183,f191,f199,f215,f224,f237,f266,f284,f293,f302,f307])).

fof(f307,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | spl4_11
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f303,f274])).

fof(f274,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK1),k2_relat_1(sK2))
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f103,f198,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t4_subset)).

fof(f198,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_28
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f103,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_11
  <=> ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f303,plain,
    ( r2_hidden(k1_funct_1(sK2,sK1),k2_relat_1(sK2))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f68,f75,f96,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t12_funct_1)).

fof(f96,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_8
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f302,plain,
    ( spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f294,f291,f300])).

fof(f300,plain,
    ( spl4_42
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f291,plain,
    ( spl4_40
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f294,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_40 ),
    inference(superposition,[],[f140,f292])).

fof(f292,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f140,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t3_subset)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',existence_m1_subset_1)).

fof(f293,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f245,f235,f81,f291])).

fof(f81,plain,
    ( spl4_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f235,plain,
    ( spl4_34
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f245,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f236,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f105,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t6_boole)).

fof(f105,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f49])).

fof(f82,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f236,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f284,plain,
    ( ~ spl4_39
    | spl4_37 ),
    inference(avatar_split_clause,[],[f267,f264,f282])).

fof(f282,plain,
    ( spl4_39
  <=> ~ r1_tarski(k1_relat_1(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f264,plain,
    ( spl4_37
  <=> ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f267,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),o_0_0_xboole_0)
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f265,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f265,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( ~ spl4_37
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f226,f169,f81,f264])).

fof(f169,plain,
    ( spl4_22
  <=> r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f226,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f170,f82,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t5_subset)).

fof(f170,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f237,plain,
    ( spl4_34
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f230,f81,f235])).

fof(f230,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f50,f227,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t2_subset)).

fof(f227,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f50,f62])).

fof(f224,plain,
    ( ~ spl4_33
    | spl4_31 ),
    inference(avatar_split_clause,[],[f216,f213,f222])).

fof(f222,plain,
    ( spl4_33
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f213,plain,
    ( spl4_31
  <=> ~ m1_subset_1(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f216,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f214,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t1_subset)).

fof(f214,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( ~ spl4_31
    | spl4_15 ),
    inference(avatar_split_clause,[],[f208,f122,f213])).

fof(f122,plain,
    ( spl4_15
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f208,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f204,f164])).

fof(f164,plain,
    ( ! [X8] :
        ( r2_hidden(X8,k1_relat_1(sK2))
        | ~ m1_subset_1(X8,k1_relat_1(sK2)) )
    | ~ spl4_15 ),
    inference(resolution,[],[f53,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_relat_1(sK2),X0)
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl4_15 ),
    inference(resolution,[],[f164,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',antisymmetry_r2_hidden)).

fof(f199,plain,
    ( spl4_28
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f192,f189,f197])).

fof(f189,plain,
    ( spl4_26
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f192,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f190,f58])).

fof(f190,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl4_26
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f184,f88,f67,f189])).

fof(f88,plain,
    ( spl4_6
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f184,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f68,f89,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',d19_relat_1)).

fof(f89,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f183,plain,
    ( ~ spl4_25
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f174,f169,f181])).

fof(f181,plain,
    ( spl4_25
  <=> ~ r2_hidden(k1_relat_1(sK2),sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f174,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK3(k1_relat_1(sK2)))
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f170,f54])).

fof(f171,plain,
    ( spl4_22
    | spl4_15 ),
    inference(avatar_split_clause,[],[f159,f122,f169])).

fof(f159,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f50,f123,f53])).

fof(f154,plain,
    ( ~ spl4_21
    | spl4_11 ),
    inference(avatar_split_clause,[],[f138,f102,f152])).

fof(f152,plain,
    ( spl4_21
  <=> ~ r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f138,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f103,f55])).

fof(f147,plain,
    ( spl4_18
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f137,f95,f145])).

fof(f145,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f137,plain,
    ( m1_subset_1(sK1,k1_relat_1(sK2))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f96,f55])).

fof(f136,plain,
    ( ~ spl4_17
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f128,f95,f134])).

fof(f134,plain,
    ( spl4_17
  <=> ~ r2_hidden(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f128,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK1)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f96,f54])).

fof(f124,plain,
    ( ~ spl4_15
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f115,f95,f122])).

fof(f115,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f96,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t7_boole)).

fof(f114,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f105,f81,f112])).

fof(f112,plain,
    ( spl4_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f104,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f47,f102])).

fof(f47,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    & r2_hidden(sK1,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
        & r2_hidden(X1,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
      & r2_hidden(sK1,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',t176_funct_1)).

fof(f97,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f48,f81])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t176_funct_1.p',dt_o_0_0_xboole_0)).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
