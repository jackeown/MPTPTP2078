%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 282 expanded)
%              Number of leaves         :   42 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  557 (1068 expanded)
%              Number of equality atoms :  150 ( 315 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f125,f139,f142,f147,f158,f165,f180,f189,f193,f321,f329,f337,f344,f358,f359,f366,f386,f396,f465,f473,f482])).

fof(f482,plain,
    ( ~ spl7_5
    | ~ spl7_56 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_56 ),
    inference(resolution,[],[f464,f111])).

fof(f111,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_5 ),
    inference(resolution,[],[f52,f98])).

fof(f98,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f464,plain,
    ( r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl7_56
  <=> r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f473,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f465,plain,
    ( spl7_56
    | ~ spl7_21
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f414,f356,f187,f463])).

fof(f187,plain,
    ( spl7_21
  <=> r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f356,plain,
    ( spl7_45
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f414,plain,
    ( r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0)
    | ~ spl7_21
    | ~ spl7_45 ),
    inference(superposition,[],[f188,f357])).

fof(f357,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f356])).

fof(f188,plain,
    ( r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f396,plain,
    ( spl7_49
    | ~ spl7_40
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f392,f382,f327,f394])).

fof(f394,plain,
    ( spl7_49
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f327,plain,
    ( spl7_40
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f382,plain,
    ( spl7_48
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f392,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_40
    | ~ spl7_48 ),
    inference(resolution,[],[f349,f383])).

fof(f383,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f382])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK3) )
    | ~ spl7_40 ),
    inference(resolution,[],[f328,f110])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f78,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f327])).

fof(f386,plain,
    ( spl7_48
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f373,f364,f335,f382])).

fof(f335,plain,
    ( spl7_42
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f364,plain,
    ( spl7_46
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f373,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(superposition,[],[f336,f365])).

fof(f365,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f364])).

fof(f336,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f335])).

fof(f366,plain,
    ( spl7_46
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f362,f353,f335,f364])).

fof(f353,plain,
    ( spl7_44
  <=> ! [X2] :
        ( ~ v1_funct_2(sK3,X2,k1_xboole_0)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f362,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(resolution,[],[f354,f336])).

fof(f354,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK3,X2,k1_xboole_0)
        | k1_xboole_0 = X2 )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f353])).

fof(f359,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK6(sK3,sK2),sK0)
    | ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f358,plain,
    ( spl7_44
    | spl7_45
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f351,f327,f356,f353])).

fof(f351,plain,
    ( ! [X2] :
        ( k1_xboole_0 = sK3
        | ~ v1_funct_2(sK3,X2,k1_xboole_0)
        | k1_xboole_0 = X2 )
    | ~ spl7_40 ),
    inference(resolution,[],[f328,f108])).

fof(f108,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f76,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f344,plain,
    ( ~ spl7_2
    | spl7_43
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f339,f319,f341,f85])).

fof(f85,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f341,plain,
    ( spl7_43
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f319,plain,
    ( spl7_39
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f339,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_39 ),
    inference(superposition,[],[f57,f320])).

fof(f320,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f319])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f337,plain,
    ( spl7_42
    | ~ spl7_3
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f324,f316,f89,f335])).

fof(f89,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f316,plain,
    ( spl7_38
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f324,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_38 ),
    inference(superposition,[],[f90,f317])).

fof(f317,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f316])).

fof(f90,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f329,plain,
    ( spl7_40
    | ~ spl7_2
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f325,f316,f85,f327])).

fof(f325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f322,f72])).

fof(f322,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_38 ),
    inference(superposition,[],[f86,f317])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f321,plain,
    ( ~ spl7_2
    | spl7_38
    | spl7_39
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f314,f89,f319,f316,f85])).

fof(f314,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f59,f90])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f193,plain,
    ( ~ spl7_10
    | ~ spl7_4
    | ~ spl7_9
    | spl7_20 ),
    inference(avatar_split_clause,[],[f190,f184,f123,f93,f128])).

fof(f128,plain,
    ( spl7_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f93,plain,
    ( spl7_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f123,plain,
    ( spl7_9
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f184,plain,
    ( spl7_20
  <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f190,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_20 ),
    inference(resolution,[],[f185,f71])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f185,plain,
    ( ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f189,plain,
    ( ~ spl7_20
    | spl7_21
    | ~ spl7_15
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f182,f178,f156,f187,f184])).

fof(f156,plain,
    ( spl7_15
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f178,plain,
    ( spl7_19
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f182,plain,
    ( r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3)
    | ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl7_15
    | ~ spl7_19 ),
    inference(superposition,[],[f179,f157])).

fof(f157,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f179,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl7_10
    | spl7_19
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f176,f93,f178,f128])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f94])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f165,plain,
    ( ~ spl7_16
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f161,f156,f163])).

fof(f163,plain,
    ( spl7_16
  <=> r2_hidden(sK6(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f161,plain,
    ( ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl7_15 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl7_15 ),
    inference(superposition,[],[f43,f157])).

fof(f43,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK2 != k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f158,plain,
    ( spl7_15
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f149,f145,f123,f156])).

fof(f145,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f149,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(resolution,[],[f146,f124])).

fof(f124,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( ~ spl7_10
    | spl7_13
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f143,f93,f145,f128])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f70,f94])).

fof(f70,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f142,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f138,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f138,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f139,plain,
    ( ~ spl7_12
    | ~ spl7_2
    | spl7_10 ),
    inference(avatar_split_clause,[],[f135,f128,f85,f137])).

fof(f135,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_2
    | spl7_10 ),
    inference(resolution,[],[f134,f86])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_10 ),
    inference(resolution,[],[f129,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f129,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f125,plain,
    ( ~ spl7_2
    | spl7_9
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f120,f81,f123,f85])).

fof(f81,plain,
    ( spl7_1
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1 ),
    inference(superposition,[],[f82,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f82,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f99,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f44,f97])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (21837)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.45  % (21837)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f483,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f125,f139,f142,f147,f158,f165,f180,f189,f193,f321,f329,f337,f344,f358,f359,f366,f386,f396,f465,f473,f482])).
% 0.20/0.47  fof(f482,plain,(
% 0.20/0.47    ~spl7_5 | ~spl7_56),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f481])).
% 0.20/0.47  fof(f481,plain,(
% 0.20/0.47    $false | (~spl7_5 | ~spl7_56)),
% 0.20/0.47    inference(resolution,[],[f464,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_5),
% 0.20/0.47    inference(resolution,[],[f52,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl7_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl7_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f464,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0) | ~spl7_56),
% 0.20/0.47    inference(avatar_component_clause,[],[f463])).
% 0.20/0.47  fof(f463,plain,(
% 0.20/0.47    spl7_56 <=> r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.20/0.47  fof(f473,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f465,plain,(
% 0.20/0.47    spl7_56 | ~spl7_21 | ~spl7_45),
% 0.20/0.47    inference(avatar_split_clause,[],[f414,f356,f187,f463])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    spl7_21 <=> r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    spl7_45 <=> k1_xboole_0 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.20/0.47  fof(f414,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK6(k1_xboole_0,sK2),sK2),k1_xboole_0) | (~spl7_21 | ~spl7_45)),
% 0.20/0.47    inference(superposition,[],[f188,f357])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    k1_xboole_0 = sK3 | ~spl7_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f356])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3) | ~spl7_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f187])).
% 0.20/0.47  fof(f396,plain,(
% 0.20/0.47    spl7_49 | ~spl7_40 | ~spl7_48),
% 0.20/0.47    inference(avatar_split_clause,[],[f392,f382,f327,f394])).
% 0.20/0.47  fof(f394,plain,(
% 0.20/0.47    spl7_49 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    spl7_40 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    spl7_48 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.20/0.47  fof(f392,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_40 | ~spl7_48)),
% 0.20/0.47    inference(resolution,[],[f349,f383])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f382])).
% 0.20/0.47  fof(f349,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_funct_2(sK3,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK3)) ) | ~spl7_40),
% 0.20/0.47    inference(resolution,[],[f328,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f78,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f328,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f327])).
% 0.20/0.47  fof(f386,plain,(
% 0.20/0.47    spl7_48 | ~spl7_42 | ~spl7_46),
% 0.20/0.47    inference(avatar_split_clause,[],[f373,f364,f335,f382])).
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    spl7_42 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    spl7_46 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_42 | ~spl7_46)),
% 0.20/0.47    inference(superposition,[],[f336,f365])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl7_46),
% 0.20/0.47    inference(avatar_component_clause,[],[f364])).
% 0.20/0.47  fof(f336,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f335])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    spl7_46 | ~spl7_42 | ~spl7_44),
% 0.20/0.47    inference(avatar_split_clause,[],[f362,f353,f335,f364])).
% 0.20/0.47  fof(f353,plain,(
% 0.20/0.47    spl7_44 <=> ! [X2] : (~v1_funct_2(sK3,X2,k1_xboole_0) | k1_xboole_0 = X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | (~spl7_42 | ~spl7_44)),
% 0.20/0.47    inference(resolution,[],[f354,f336])).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    ( ! [X2] : (~v1_funct_2(sK3,X2,k1_xboole_0) | k1_xboole_0 = X2) ) | ~spl7_44),
% 0.20/0.47    inference(avatar_component_clause,[],[f353])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    sK0 != k1_relat_1(sK3) | r2_hidden(sK6(sK3,sK2),sK0) | ~r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f358,plain,(
% 0.20/0.47    spl7_44 | spl7_45 | ~spl7_40),
% 0.20/0.47    inference(avatar_split_clause,[],[f351,f327,f356,f353])).
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 = sK3 | ~v1_funct_2(sK3,X2,k1_xboole_0) | k1_xboole_0 = X2) ) | ~spl7_40),
% 0.20/0.47    inference(resolution,[],[f328,f108])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f76,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    ~spl7_2 | spl7_43 | ~spl7_39),
% 0.20/0.47    inference(avatar_split_clause,[],[f339,f319,f341,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f341,plain,(
% 0.20/0.47    spl7_43 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.20/0.47  fof(f319,plain,(
% 0.20/0.47    spl7_39 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.20/0.47  fof(f339,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_39),
% 0.20/0.47    inference(superposition,[],[f57,f320])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_39),
% 0.20/0.47    inference(avatar_component_clause,[],[f319])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f337,plain,(
% 0.20/0.47    spl7_42 | ~spl7_3 | ~spl7_38),
% 0.20/0.47    inference(avatar_split_clause,[],[f324,f316,f89,f335])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl7_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f316,plain,(
% 0.20/0.47    spl7_38 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl7_3 | ~spl7_38)),
% 0.20/0.47    inference(superposition,[],[f90,f317])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl7_38),
% 0.20/0.47    inference(avatar_component_clause,[],[f316])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f329,plain,(
% 0.20/0.47    spl7_40 | ~spl7_2 | ~spl7_38),
% 0.20/0.47    inference(avatar_split_clause,[],[f325,f316,f85,f327])).
% 0.20/0.47  fof(f325,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_38)),
% 0.20/0.47    inference(forward_demodulation,[],[f322,f72])).
% 0.20/0.47  fof(f322,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_38)),
% 0.20/0.47    inference(superposition,[],[f86,f317])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    ~spl7_2 | spl7_38 | spl7_39 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f314,f89,f319,f316,f85])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.20/0.47    inference(resolution,[],[f59,f90])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ~spl7_10 | ~spl7_4 | ~spl7_9 | spl7_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f190,f184,f123,f93,f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl7_10 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl7_4 <=> v1_funct_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl7_9 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    spl7_20 <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~r2_hidden(sK2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl7_20),
% 0.20/0.47    inference(resolution,[],[f185,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ~r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | spl7_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f184])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~spl7_20 | spl7_21 | ~spl7_15 | ~spl7_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f182,f178,f156,f187,f184])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl7_15 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl7_19 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK6(sK3,sK2),sK2),sK3) | ~r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | (~spl7_15 | ~spl7_19)),
% 0.20/0.47    inference(superposition,[],[f179,f157])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~spl7_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl7_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f178])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~spl7_10 | spl7_19 | ~spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f176,f93,f178,f128])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 0.20/0.47    inference(resolution,[],[f79,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    v1_funct_1(sK3) | ~spl7_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(equality_resolution,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~spl7_16 | ~spl7_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f161,f156,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl7_16 <=> r2_hidden(sK6(sK3,sK2),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl7_15),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f159])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    sK2 != sK2 | ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl7_15),
% 0.20/0.47    inference(superposition,[],[f43,f157])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl7_15 | ~spl7_9 | ~spl7_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f149,f145,f123,f156])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl7_13 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | (~spl7_9 | ~spl7_13)),
% 0.20/0.47    inference(resolution,[],[f146,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl7_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0) ) | ~spl7_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f145])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl7_10 | spl7_13 | ~spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f143,f93,f145,f128])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 0.20/0.47    inference(resolution,[],[f70,f94])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    spl7_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    $false | spl7_12),
% 0.20/0.47    inference(resolution,[],[f138,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f137])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    spl7_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ~spl7_12 | ~spl7_2 | spl7_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f135,f128,f85,f137])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_2 | spl7_10)),
% 0.20/0.47    inference(resolution,[],[f134,f86])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_10),
% 0.20/0.47    inference(resolution,[],[f129,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl7_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f128])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~spl7_2 | spl7_9 | ~spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f120,f81,f123,f85])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl7_1 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_1),
% 0.20/0.47    inference(superposition,[],[f82,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl7_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f97])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f93])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f89])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f85])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f81])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21837)------------------------------
% 0.20/0.47  % (21837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21837)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21837)Memory used [KB]: 11001
% 0.20/0.47  % (21837)Time elapsed: 0.049 s
% 0.20/0.47  % (21837)------------------------------
% 0.20/0.47  % (21837)------------------------------
% 0.20/0.48  % (21828)Success in time 0.115 s
%------------------------------------------------------------------------------
