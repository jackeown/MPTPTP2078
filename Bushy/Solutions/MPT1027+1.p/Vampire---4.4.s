%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t130_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 424 expanded)
%              Number of leaves         :   58 ( 177 expanded)
%              Depth                    :   10
%              Number of atoms          :  508 (1063 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f104,f111,f121,f136,f146,f156,f169,f177,f195,f199,f206,f219,f223,f230,f247,f261,f277,f295,f300,f307,f341,f350,f364,f377,f378,f379,f391,f401,f413,f423,f429])).

fof(f429,plain,
    ( ~ spl4_0
    | ~ spl4_12
    | spl4_27
    | ~ spl4_58
    | ~ spl4_64 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_58
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f427,f205])).

fof(f205,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_27
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f427,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_58
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f426,f390])).

fof(f390,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl4_58
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f426,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl4_0
    | ~ spl4_12
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f425,f135])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f425,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_0
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f424,f82])).

fof(f82,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f424,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_64 ),
    inference(resolution,[],[f422,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t4_funct_2)).

fof(f422,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl4_64
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f423,plain,
    ( spl4_64
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f415,f411,f421])).

fof(f411,plain,
    ( spl4_62
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f415,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_62 ),
    inference(resolution,[],[f412,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t3_subset)).

fof(f412,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f411])).

fof(f413,plain,
    ( spl4_62
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f406,f399,f102,f411])).

fof(f102,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f399,plain,
    ( spl4_60
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f406,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f404,f400])).

fof(f400,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f399])).

fof(f404,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f72,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',dt_k2_relset_1)).

fof(f401,plain,
    ( spl4_60
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f394,f102,f399])).

fof(f394,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f71,f103])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',redefinition_k2_relset_1)).

fof(f391,plain,
    ( spl4_58
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f384,f109,f102,f389])).

fof(f109,plain,
    ( spl4_8
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f384,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f383,f110])).

fof(f110,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f383,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f70,f103])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',redefinition_k1_relset_1)).

fof(f379,plain,
    ( spl4_52
    | spl4_42
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f342,f333,f275,f348])).

fof(f348,plain,
    ( spl4_52
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f275,plain,
    ( spl4_42
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f333,plain,
    ( spl4_48
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f342,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_48 ),
    inference(resolution,[],[f334,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t2_subset)).

fof(f334,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f333])).

fof(f378,plain,
    ( spl4_40
    | spl4_42
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f296,f245,f275,f269])).

fof(f269,plain,
    ( spl4_40
  <=> r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f245,plain,
    ( spl4_36
  <=> m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f296,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_36 ),
    inference(resolution,[],[f246,f62])).

fof(f246,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f245])).

fof(f377,plain,
    ( ~ spl4_57
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f369,f348,f375])).

fof(f375,plain,
    ( spl4_57
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f369,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl4_52 ),
    inference(resolution,[],[f349,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',antisymmetry_r2_hidden)).

fof(f349,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f348])).

fof(f364,plain,
    ( spl4_54
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f355,f275,f154,f144,f362])).

fof(f362,plain,
    ( spl4_54
  <=> k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f144,plain,
    ( spl4_14
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f154,plain,
    ( spl4_16
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f355,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f351,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f351,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_42 ),
    inference(resolution,[],[f276,f148])).

fof(f148,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_14 ),
    inference(resolution,[],[f145,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t8_boole)).

fof(f145,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f276,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f275])).

fof(f350,plain,
    ( spl4_52
    | spl4_43
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f343,f333,f272,f348])).

fof(f272,plain,
    ( spl4_43
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f343,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_43
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f342,f273])).

fof(f273,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f272])).

fof(f341,plain,
    ( spl4_48
    | spl4_50
    | ~ spl4_6
    | spl4_35 ),
    inference(avatar_split_clause,[],[f328,f236,f102,f339,f333])).

fof(f339,plain,
    ( spl4_50
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f236,plain,
    ( spl4_35
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f328,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f324,f237])).

fof(f237,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f236])).

fof(f324,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f312,f232])).

fof(f232,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f74,f103])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t4_subset)).

fof(f312,plain,(
    ! [X6] :
      ( r2_hidden(sK3(sK3(k1_zfmisc_1(X6))),X6)
      | v1_xboole_0(X6)
      | v1_xboole_0(sK3(k1_zfmisc_1(X6))) ) ),
    inference(resolution,[],[f263,f62])).

fof(f263,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f231,f123])).

fof(f123,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',existence_m1_subset_1)).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f74,f59])).

fof(f307,plain,
    ( ~ spl4_47
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f298,f269,f305])).

fof(f305,plain,
    ( spl4_47
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f298,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK2))
    | ~ spl4_40 ),
    inference(resolution,[],[f270,f60])).

fof(f270,plain,
    ( r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f269])).

fof(f300,plain,
    ( ~ spl4_43
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f299,f269,f272])).

fof(f299,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_40 ),
    inference(resolution,[],[f270,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t7_boole)).

fof(f295,plain,
    ( spl4_44
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f280,f259,f81,f293])).

fof(f293,plain,
    ( spl4_44
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f259,plain,
    ( spl4_38
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f280,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(superposition,[],[f82,f260])).

fof(f260,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f259])).

fof(f277,plain,
    ( spl4_40
    | spl4_42
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f262,f245,f275,f269])).

fof(f262,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_36 ),
    inference(resolution,[],[f246,f62])).

fof(f261,plain,
    ( spl4_38
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f252,f239,f154,f144,f259])).

fof(f239,plain,
    ( spl4_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f252,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f248,f155])).

fof(f248,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_34 ),
    inference(resolution,[],[f240,f148])).

fof(f240,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f239])).

fof(f247,plain,
    ( spl4_34
    | spl4_36
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f234,f102,f245,f239])).

fof(f234,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f232,f123])).

fof(f230,plain,
    ( ~ spl4_33
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f221,f211,f228])).

fof(f228,plain,
    ( spl4_33
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f211,plain,
    ( spl4_28
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f221,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl4_28 ),
    inference(resolution,[],[f212,f60])).

fof(f212,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f211])).

fof(f223,plain,
    ( ~ spl4_31
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f222,f211,f214])).

fof(f214,plain,
    ( spl4_31
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f222,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_28 ),
    inference(resolution,[],[f212,f68])).

fof(f219,plain,
    ( spl4_28
    | spl4_30
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f124,f102,f217,f211])).

fof(f217,plain,
    ( spl4_30
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f124,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(resolution,[],[f62,f103])).

fof(f206,plain,
    ( ~ spl4_1
    | ~ spl4_27
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f55,f99,f204,f78])).

fof(f78,plain,
    ( spl4_1
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( spl4_7
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & k1_relset_1(sK0,sK1,sK2) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & k1_relset_1(sK0,sK1,sK2) = sK0
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t130_funct_2)).

fof(f199,plain,
    ( ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f198,f193,f184])).

fof(f184,plain,
    ( spl4_23
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f193,plain,
    ( spl4_24
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f198,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24 ),
    inference(resolution,[],[f194,f68])).

fof(f194,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl4_22
    | spl4_24
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f161,f154,f193,f187])).

fof(f187,plain,
    ( spl4_22
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f161,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f123,f155])).

fof(f177,plain,
    ( spl4_20
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f162,f154,f175])).

fof(f175,plain,
    ( spl4_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f162,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f59,f155])).

fof(f169,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f159,f154,f167])).

fof(f167,plain,
    ( spl4_18
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f159,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_16 ),
    inference(superposition,[],[f113,f155])).

fof(f113,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f66,f59])).

fof(f156,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f149,f144,f154])).

fof(f149,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(resolution,[],[f145,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t6_boole)).

fof(f146,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f139,f88,f144])).

fof(f88,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f139,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f138,f123])).

fof(f138,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f137,f59])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',t5_subset)).

fof(f136,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f129,f102,f134])).

fof(f129,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f103])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',cc1_relset_1)).

fof(f121,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f114,f102,f119])).

fof(f119,plain,
    ( spl4_10
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f114,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f103])).

fof(f111,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f57,f95])).

fof(f95,plain,
    ( spl4_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',d2_xboole_0)).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f76,f88])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t130_funct_2.p',dt_o_0_0_xboole_0)).

fof(f83,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f52,f81])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
