%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t19_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 273 expanded)
%              Number of leaves         :   42 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  339 ( 591 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f98,f108,f115,f130,f145,f155,f167,f181,f202,f211,f220,f229,f238,f261,f274,f291,f320,f329,f345,f354,f420,f429])).

fof(f429,plain,
    ( spl4_7
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f427,f114])).

fof(f114,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f427,plain,
    ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f426,f228])).

fof(f228,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_24
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f426,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f425,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',commutativity_k2_xboole_0)).

fof(f425,plain,
    ( r1_tarski(k2_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f357,f65])).

fof(f357,plain,
    ( r1_tarski(k2_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)),k2_xboole_0(sK1,sK0))
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f328,f353,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t13_xboole_1)).

fof(f353,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl4_42
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f328,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_38
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f420,plain,
    ( spl4_7
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f418,f114])).

fof(f418,plain,
    ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | ~ spl4_24
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f361,f228])).

fof(f361,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f353,f328,f80])).

fof(f354,plain,
    ( spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f346,f343,f352])).

fof(f343,plain,
    ( spl4_40
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f346,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f344,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t3_subset)).

fof(f344,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f343])).

fof(f345,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f337,f236,f106,f343])).

fof(f106,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f236,plain,
    ( spl4_26
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f337,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f330,f237])).

fof(f237,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f330,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',dt_k1_relset_1)).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f329,plain,
    ( spl4_38
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f321,f318,f327])).

fof(f318,plain,
    ( spl4_36
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f321,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f319,f69])).

fof(f319,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f318])).

fof(f320,plain,
    ( spl4_36
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f298,f259,f106,f318])).

fof(f259,plain,
    ( spl4_28
  <=> k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f298,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f293,f260])).

fof(f260,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f293,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',dt_k2_relset_1)).

fof(f291,plain,
    ( ~ spl4_35
    | ~ spl4_0
    | spl4_31 ),
    inference(avatar_split_clause,[],[f281,f263,f85,f289])).

fof(f289,plain,
    ( spl4_35
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f85,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f263,plain,
    ( spl4_31
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f281,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f86,f264,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t8_boole)).

fof(f264,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f263])).

fof(f86,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f85])).

fof(f274,plain,
    ( spl4_30
    | spl4_32
    | ~ spl4_0
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f241,f218,f85,f272,f266])).

fof(f266,plain,
    ( spl4_30
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f272,plain,
    ( spl4_32
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f218,plain,
    ( spl4_22
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f241,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_0
    | ~ spl4_22 ),
    inference(resolution,[],[f158,f219])).

fof(f219,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f158,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl4_0 ),
    inference(resolution,[],[f68,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_0 ),
    inference(backward_demodulation,[],[f88,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t6_boole)).

fof(f88,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f86,f62])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t2_subset)).

fof(f261,plain,
    ( spl4_28
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f254,f106,f259])).

fof(f254,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',redefinition_k2_relset_1)).

fof(f238,plain,
    ( spl4_26
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f231,f106,f236])).

fof(f231,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',redefinition_k1_relset_1)).

fof(f229,plain,
    ( spl4_24
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f170,f165,f227])).

fof(f165,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f170,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f166,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',d6_relat_1)).

fof(f166,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f220,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f204,f200,f218])).

fof(f200,plain,
    ( spl4_18
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f204,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(superposition,[],[f63,f201])).

fof(f201,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',existence_m1_subset_1)).

fof(f211,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f203,f200,f209])).

fof(f209,plain,
    ( spl4_20
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f203,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_18 ),
    inference(superposition,[],[f121,f201])).

fof(f121,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f63,f69])).

fof(f202,plain,
    ( spl4_18
    | ~ spl4_0
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f187,f179,f85,f200])).

fof(f179,plain,
    ( spl4_16
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f187,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f180,f90])).

fof(f180,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( spl4_16
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f169,f85,f179])).

fof(f169,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f63,f168,f68])).

fof(f168,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f86,f63,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t5_subset)).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f160,f106,f165])).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',cc1_relset_1)).

fof(f155,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f147,f143,f153])).

fof(f153,plain,
    ( spl4_13
  <=> ~ r2_hidden(k3_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f143,plain,
    ( spl4_11
  <=> ~ m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f147,plain,
    ( ~ r2_hidden(k3_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f144,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t1_subset)).

fof(f144,plain,
    ( ~ m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( ~ spl4_11
    | spl4_7 ),
    inference(avatar_split_clause,[],[f120,f113,f143])).

fof(f120,plain,
    ( ~ m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f114,f69])).

fof(f130,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f122,f106,f128])).

fof(f128,plain,
    ( spl4_8
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f122,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f107,f69])).

fof(f115,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f58,f113])).

fof(f58,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',t19_relset_1)).

fof(f108,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,
    ( spl4_2
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f88,f85,f96])).

fof(f96,plain,
    ( spl4_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f59,f85])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t19_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
