%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t27_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 343 expanded)
%              Number of leaves         :   44 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  417 ( 884 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f78,f85,f92,f99,f106,f113,f136,f147,f159,f167,f186,f193,f207,f226,f234,f253,f262,f269,f276,f296,f310,f322,f329,f340,f347,f358,f364])).

fof(f364,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5
    | ~ spl3_12
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f362,f70])).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f362,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f361,f77])).

fof(f77,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f361,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f360,f112])).

fof(f112,plain,
    ( v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_12
  <=> v1_finset_1(k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f360,plain,
    ( ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f359,f84])).

fof(f84,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_5
  <=> ~ v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f359,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_56 ),
    inference(superposition,[],[f56,f357])).

fof(f357,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl3_56
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',fc13_finset_1)).

fof(f358,plain,
    ( spl3_56
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f350,f104,f76,f69,f356])).

fof(f104,plain,
    ( spl3_10
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f350,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f333,f105])).

fof(f105,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 )
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f332,f70])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f77])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t147_funct_1)).

fof(f347,plain,
    ( ~ spl3_55
    | spl3_51 ),
    inference(avatar_split_clause,[],[f331,f327,f345])).

fof(f345,plain,
    ( spl3_55
  <=> ~ r2_hidden(k1_zfmisc_1(k2_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f327,plain,
    ( spl3_51
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f331,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_51 ),
    inference(resolution,[],[f328,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t1_subset)).

fof(f328,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f327])).

fof(f340,plain,
    ( ~ spl3_53
    | spl3_51 ),
    inference(avatar_split_clause,[],[f330,f327,f338])).

fof(f338,plain,
    ( spl3_53
  <=> ~ r1_tarski(k1_zfmisc_1(k2_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f330,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k2_relat_1(sK1)),k1_xboole_0)
    | ~ spl3_51 ),
    inference(resolution,[],[f328,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t3_subset)).

fof(f329,plain,
    ( ~ spl3_51
    | ~ spl3_6
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f313,f294,f90,f327])).

fof(f90,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f294,plain,
    ( spl3_44
  <=> r2_hidden(sK0,k1_zfmisc_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f313,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_44 ),
    inference(resolution,[],[f295,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f63,f91])).

fof(f91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t5_subset)).

fof(f295,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(k2_relat_1(sK1)))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f294])).

fof(f322,plain,
    ( ~ spl3_49
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f314,f294,f320])).

fof(f320,plain,
    ( spl3_49
  <=> ~ r2_hidden(k1_zfmisc_1(k2_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f314,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_relat_1(sK1)),sK0)
    | ~ spl3_44 ),
    inference(resolution,[],[f295,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',antisymmetry_r2_hidden)).

fof(f310,plain,
    ( spl3_46
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f301,f288,f145,f134,f308])).

fof(f308,plain,
    ( spl3_46
  <=> k1_xboole_0 = k1_zfmisc_1(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f134,plain,
    ( spl3_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f145,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f288,plain,
    ( spl3_42
  <=> v1_xboole_0(k1_zfmisc_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f301,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k2_relat_1(sK1))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f297,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f297,plain,
    ( k1_zfmisc_1(k2_relat_1(sK1)) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(resolution,[],[f289,f138])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK2(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl3_14 ),
    inference(resolution,[],[f135,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t8_boole)).

fof(f135,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f289,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_relat_1(sK1)))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f288])).

fof(f296,plain,
    ( spl3_42
    | spl3_44
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f281,f104,f294,f288])).

fof(f281,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(k2_relat_1(sK1)))
    | v1_xboole_0(k1_zfmisc_1(k2_relat_1(sK1)))
    | ~ spl3_10 ),
    inference(resolution,[],[f121,f105])).

fof(f121,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f55,f59])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t2_subset)).

fof(f276,plain,
    ( spl3_40
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f239,f224,f145,f134,f274])).

fof(f274,plain,
    ( spl3_40
  <=> k1_xboole_0 = sK2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f224,plain,
    ( spl3_30
  <=> v1_xboole_0(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f239,plain,
    ( k1_xboole_0 = sK2(k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f235,f146])).

fof(f235,plain,
    ( sK2(k1_xboole_0) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_30 ),
    inference(resolution,[],[f225,f138])).

fof(f225,plain,
    ( v1_xboole_0(sK2(k1_xboole_0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f269,plain,
    ( ~ spl3_39
    | spl3_35 ),
    inference(avatar_split_clause,[],[f255,f251,f267])).

fof(f267,plain,
    ( spl3_39
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f251,plain,
    ( spl3_35
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f255,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_35 ),
    inference(resolution,[],[f252,f54])).

fof(f252,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f251])).

fof(f262,plain,
    ( ~ spl3_37
    | spl3_35 ),
    inference(avatar_split_clause,[],[f254,f251,f260])).

fof(f260,plain,
    ( spl3_37
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f254,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_35 ),
    inference(resolution,[],[f252,f59])).

fof(f253,plain,
    ( ~ spl3_35
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f244,f191,f90,f251])).

fof(f191,plain,
    ( spl3_26
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f244,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(resolution,[],[f192,f125])).

fof(f192,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f234,plain,
    ( spl3_32
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f212,f205,f165,f232])).

fof(f232,plain,
    ( spl3_32
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f165,plain,
    ( spl3_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f205,plain,
    ( spl3_28
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f212,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(superposition,[],[f166,f206])).

fof(f206,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f205])).

fof(f166,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f226,plain,
    ( spl3_30
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f210,f205,f134,f224])).

fof(f210,plain,
    ( v1_xboole_0(sK2(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(superposition,[],[f135,f206])).

fof(f207,plain,
    ( spl3_28
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f198,f178,f145,f134,f205])).

fof(f178,plain,
    ( spl3_22
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f198,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f194,f146])).

fof(f194,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(resolution,[],[f179,f138])).

fof(f179,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f193,plain,
    ( spl3_22
    | spl3_26
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f151,f145,f191,f178])).

fof(f151,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(superposition,[],[f119,f146])).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',existence_m1_subset_1)).

fof(f186,plain,
    ( spl3_22
    | ~ spl3_25
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f150,f145,f184,f178])).

fof(f184,plain,
    ( spl3_25
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f150,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(superposition,[],[f122,f146])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f53])).

fof(f167,plain,
    ( spl3_20
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f152,f145,f165])).

fof(f152,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f146])).

fof(f159,plain,
    ( spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f149,f145,f157])).

fof(f157,plain,
    ( spl3_18
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f149,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(superposition,[],[f115,f146])).

fof(f115,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f58,f52])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f147,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f139,f134,f145])).

fof(f139,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14 ),
    inference(resolution,[],[f135,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t6_boole)).

fof(f136,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f127,f90,f134])).

fof(f127,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f126,f52])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f125,f119])).

fof(f113,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f47,f111])).

fof(f47,plain,(
    v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',t27_finset_1)).

fof(f106,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f46,f104])).

fof(f46,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f97])).

fof(f97,plain,
    ( spl3_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f50,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',d2_xboole_0)).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f64,f90])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f49,f50])).

fof(f49,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t27_finset_1.p',dt_o_0_0_xboole_0)).

fof(f85,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f44,f69])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
