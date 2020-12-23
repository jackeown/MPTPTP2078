%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0966+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 365 expanded)
%              Number of leaves         :   55 ( 164 expanded)
%              Depth                    :    9
%              Number of atoms          :  553 (1196 expanded)
%              Number of equality atoms :  114 ( 267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f91,f96,f101,f106,f107,f112,f132,f138,f258,f287,f323,f340,f383,f389,f450,f457,f465,f479,f518,f529,f610,f611,f707,f738,f786,f816,f860,f866,f876,f878,f885,f890,f896,f903,f1019,f1122])).

fof(f1122,plain,
    ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
    | v1_xboole_0(k2_relat_1(sK6))
    | ~ v1_xboole_0(k2_relset_1(sK3,sK4,sK6)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1019,plain,
    ( spl7_5
    | ~ spl7_42
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f1018,f778,f429,f88])).

fof(f88,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f429,plain,
    ( spl7_42
  <=> k1_xboole_0 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f778,plain,
    ( spl7_71
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f1018,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_42
    | ~ spl7_71 ),
    inference(backward_demodulation,[],[f780,f430])).

fof(f430,plain,
    ( k1_xboole_0 = k1_relat_1(sK6)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f429])).

fof(f780,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f778])).

fof(f903,plain,
    ( ~ spl7_39
    | spl7_44 ),
    inference(avatar_split_clause,[],[f483,f452,f398])).

fof(f398,plain,
    ( spl7_39
  <=> v1_xboole_0(k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f452,plain,
    ( spl7_44
  <=> k1_xboole_0 = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f483,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK6))
    | spl7_44 ),
    inference(unit_resulting_resolution,[],[f454,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f454,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | spl7_44 ),
    inference(avatar_component_clause,[],[f452])).

fof(f896,plain,
    ( ~ spl7_10
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f868,f853,f119])).

fof(f119,plain,
    ( spl7_10
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f853,plain,
    ( spl7_75
  <=> sP0(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f868,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_75 ),
    inference(unit_resulting_resolution,[],[f855,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f69,f49])).

fof(f69,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f855,plain,
    ( sP0(sK3,sK5)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f853])).

fof(f890,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | k1_xboole_0 != sK3
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f885,plain,
    ( k1_xboole_0 != sK5
    | r1_tarski(k2_relset_1(sK3,sK4,sK6),k1_xboole_0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f878,plain,
    ( k1_relat_1(sK6) != k1_relset_1(sK3,sK5,sK6)
    | k1_xboole_0 != k1_relat_1(sK6)
    | k1_xboole_0 != sK3
    | sK3 = k1_relset_1(sK3,sK5,sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f876,plain,
    ( spl7_76
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f869,f853,f872])).

fof(f872,plain,
    ( spl7_76
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f869,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_75 ),
    inference(resolution,[],[f855,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f866,plain,
    ( k1_xboole_0 != sK3
    | ~ m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))
    | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f860,plain,
    ( spl7_75
    | spl7_2
    | ~ spl7_63
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f859,f813,f695,f75,f853])).

fof(f75,plain,
    ( spl7_2
  <=> v1_funct_2(sK6,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f695,plain,
    ( spl7_63
  <=> sP1(sK3,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f813,plain,
    ( spl7_74
  <=> sK3 = k1_relset_1(sK3,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f859,plain,
    ( sP0(sK3,sK5)
    | spl7_2
    | ~ spl7_63
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f858,f697])).

fof(f697,plain,
    ( sP1(sK3,sK6,sK5)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f695])).

fof(f858,plain,
    ( sP0(sK3,sK5)
    | ~ sP1(sK3,sK6,sK5)
    | spl7_2
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f850,f77])).

fof(f77,plain,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f850,plain,
    ( v1_funct_2(sK6,sK3,sK5)
    | sP0(sK3,sK5)
    | ~ sP1(sK3,sK6,sK5)
    | ~ spl7_74 ),
    inference(trivial_inequality_removal,[],[f847])).

fof(f847,plain,
    ( sK3 != sK3
    | v1_funct_2(sK6,sK3,sK5)
    | sP0(sK3,sK5)
    | ~ sP1(sK3,sK6,sK5)
    | ~ spl7_74 ),
    inference(superposition,[],[f61,f815])).

fof(f815,plain,
    ( sK3 = k1_relset_1(sK3,sK5,sK6)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f813])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f816,plain,
    ( spl7_74
    | ~ spl7_66
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f800,f778,f735,f813])).

fof(f735,plain,
    ( spl7_66
  <=> k1_relat_1(sK6) = k1_relset_1(sK3,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f800,plain,
    ( sK3 = k1_relset_1(sK3,sK5,sK6)
    | ~ spl7_66
    | ~ spl7_71 ),
    inference(backward_demodulation,[],[f737,f780])).

fof(f737,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK3,sK5,sK6)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f735])).

fof(f786,plain,
    ( spl7_71
    | spl7_4
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f785,f476,f336,f103,f84,f778])).

fof(f84,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f103,plain,
    ( spl7_8
  <=> v1_funct_2(sK6,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f336,plain,
    ( spl7_34
  <=> sP1(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f476,plain,
    ( spl7_47
  <=> k1_relat_1(sK6) = k1_relset_1(sK3,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f785,plain,
    ( sK3 = k1_relat_1(sK6)
    | spl7_4
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f784,f338])).

fof(f338,plain,
    ( sP1(sK3,sK6,sK4)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f336])).

fof(f784,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ sP1(sK3,sK6,sK4)
    | spl7_4
    | ~ spl7_8
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f783,f142])).

fof(f142,plain,
    ( ! [X0] : ~ sP0(X0,sK4)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f86,f62])).

fof(f86,plain,
    ( k1_xboole_0 != sK4
    | spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f783,plain,
    ( sK3 = k1_relat_1(sK6)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK6,sK4)
    | ~ spl7_8
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f767,f105])).

fof(f105,plain,
    ( v1_funct_2(sK6,sK3,sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f767,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK6,sK4)
    | ~ spl7_47 ),
    inference(superposition,[],[f478,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f478,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK3,sK4,sK6)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f476])).

fof(f738,plain,
    ( spl7_66
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f714,f79,f735])).

fof(f79,plain,
    ( spl7_3
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f714,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK3,sK5,sK6)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f707,plain,
    ( spl7_63
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f686,f158,f695])).

fof(f158,plain,
    ( spl7_15
  <=> r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f686,plain,
    ( sP1(sK3,sK6,sK5)
    | ~ spl7_15 ),
    inference(resolution,[],[f159,f334])).

fof(f334,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f26,f29,f28,f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f159,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK5))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f611,plain,
    ( ~ spl7_3
    | spl7_15 ),
    inference(avatar_split_clause,[],[f168,f158,f79])).

fof(f168,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f160,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f160,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK5))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f610,plain,
    ( spl7_3
    | ~ spl7_28
    | ~ spl7_37
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f574,f525,f386,f254,f79])).

fof(f254,plain,
    ( spl7_28
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f386,plain,
    ( spl7_37
  <=> r1_tarski(k2_relat_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f525,plain,
    ( spl7_49
  <=> r1_tarski(k1_relat_1(sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f574,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl7_28
    | ~ spl7_37
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f256,f527,f388,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f388,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f386])).

fof(f527,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f525])).

fof(f256,plain,
    ( v1_relat_1(sK6)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f529,plain,
    ( spl7_49
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f522,f515,f525])).

fof(f515,plain,
    ( spl7_48
  <=> m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f522,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ spl7_48 ),
    inference(resolution,[],[f517,f51])).

fof(f517,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f515])).

fof(f518,plain,
    ( spl7_48
    | ~ spl7_7
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f513,f476,f98,f515])).

fof(f98,plain,
    ( spl7_7
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f513,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))
    | ~ spl7_7
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f505,f478])).

fof(f505,plain,
    ( m1_subset_1(k1_relset_1(sK3,sK4,sK6),k1_zfmisc_1(sK3))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f100,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f479,plain,
    ( spl7_47
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f474,f98,f476])).

fof(f474,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK3,sK4,sK6)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f100,f56])).

fof(f465,plain,
    ( ~ spl7_45
    | ~ spl7_13
    | spl7_43 ),
    inference(avatar_split_clause,[],[f459,f445,f135,f462])).

fof(f462,plain,
    ( spl7_45
  <=> m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f135,plain,
    ( spl7_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f445,plain,
    ( spl7_43
  <=> v1_xboole_0(k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f459,plain,
    ( ~ m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_13
    | spl7_43 ),
    inference(unit_resulting_resolution,[],[f137,f447,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f447,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK6))
    | spl7_43 ),
    inference(avatar_component_clause,[],[f445])).

fof(f137,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f457,plain,
    ( ~ spl7_44
    | ~ spl7_28
    | spl7_42 ),
    inference(avatar_split_clause,[],[f456,f429,f254,f452])).

fof(f456,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ spl7_28
    | spl7_42 ),
    inference(subsumption_resolution,[],[f443,f256])).

fof(f443,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_42 ),
    inference(trivial_inequality_removal,[],[f442])).

fof(f442,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_42 ),
    inference(superposition,[],[f431,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f431,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f429])).

fof(f450,plain,
    ( ~ spl7_43
    | spl7_42 ),
    inference(avatar_split_clause,[],[f439,f429,f445])).

fof(f439,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK6))
    | spl7_42 ),
    inference(unit_resulting_resolution,[],[f431,f49])).

fof(f389,plain,
    ( spl7_37
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f384,f98,f93,f386])).

fof(f93,plain,
    ( spl7_6
  <=> r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f384,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f372,f100])).

fof(f372,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl7_6 ),
    inference(superposition,[],[f95,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f95,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f383,plain,
    ( spl7_36
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f371,f98,f380])).

fof(f380,plain,
    ( spl7_36
  <=> k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f371,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f100,f55])).

fof(f340,plain,
    ( spl7_34
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f333,f98,f336])).

fof(f333,plain,
    ( sP1(sK3,sK6,sK4)
    | ~ spl7_7 ),
    inference(resolution,[],[f64,f100])).

fof(f323,plain,
    ( ~ spl7_33
    | spl7_31 ),
    inference(avatar_split_clause,[],[f316,f284,f319])).

fof(f319,plain,
    ( spl7_33
  <=> r1_tarski(k2_relset_1(sK3,sK4,sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f284,plain,
    ( spl7_31
  <=> m1_subset_1(k2_relset_1(sK3,sK4,sK6),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f316,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK6),k1_xboole_0)
    | spl7_31 ),
    inference(resolution,[],[f286,f52])).

fof(f286,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK6),k1_zfmisc_1(k1_xboole_0))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f284])).

fof(f287,plain,
    ( ~ spl7_31
    | ~ spl7_13
    | spl7_22 ),
    inference(avatar_split_clause,[],[f281,f205,f135,f284])).

fof(f205,plain,
    ( spl7_22
  <=> v1_xboole_0(k2_relset_1(sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f281,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK6),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_13
    | spl7_22 ),
    inference(unit_resulting_resolution,[],[f137,f206,f50])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_relset_1(sK3,sK4,sK6))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f258,plain,
    ( spl7_28
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f251,f98,f254])).

fof(f251,plain,
    ( v1_relat_1(sK6)
    | ~ spl7_7 ),
    inference(resolution,[],[f54,f100])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,
    ( spl7_13
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f133,f129,f109,f135])).

fof(f109,plain,
    ( spl7_9
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f129,plain,
    ( spl7_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f133,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f111,f131])).

fof(f131,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f111,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f132,plain,
    ( spl7_12
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f113,f109,f129])).

fof(f113,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f111,f49])).

fof(f112,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f46,f109])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f107,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f71,plain,
    ( spl7_1
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f40,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
      | ~ v1_funct_2(sK6,sK3,sK5)
      | ~ v1_funct_1(sK6) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
        | ~ v1_funct_2(sK6,sK3,sK5)
        | ~ v1_funct_1(sK6) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f106,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f41,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f42,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f43,f93])).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f44,f88,f84])).

fof(f44,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f45,f79,f75,f71])).

fof(f45,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
