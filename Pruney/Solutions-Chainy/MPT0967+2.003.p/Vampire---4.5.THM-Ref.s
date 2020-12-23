%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 325 expanded)
%              Number of leaves         :   38 ( 132 expanded)
%              Depth                    :    9
%              Number of atoms          :  516 (1260 expanded)
%              Number of equality atoms :  109 ( 342 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f115,f119,f123,f127,f129,f141,f220,f236,f250,f258,f267,f276,f280,f293,f312,f321,f332,f338,f357,f381,f444,f454,f468,f485,f488,f527])).

fof(f527,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f488,plain,
    ( ~ spl5_48
    | ~ spl5_22
    | spl5_33 ),
    inference(avatar_split_clause,[],[f486,f318,f256,f483])).

fof(f483,plain,
    ( spl5_48
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f256,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f318,plain,
    ( spl5_33
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f486,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(sK3)
    | spl5_33 ),
    inference(forward_demodulation,[],[f365,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f365,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl5_33 ),
    inference(superposition,[],[f319,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f319,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f318])).

fof(f485,plain,
    ( ~ spl5_17
    | ~ spl5_1
    | ~ spl5_38
    | spl5_48
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f369,f310,f483,f373,f100,f215])).

fof(f215,plain,
    ( spl5_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f100,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f373,plain,
    ( spl5_38
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f310,plain,
    ( spl5_32
  <=> ! [X1] :
        ( ~ v1_funct_2(sK3,X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f369,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_32 ),
    inference(resolution,[],[f311,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f311,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f310])).

fof(f468,plain,
    ( ~ spl5_3
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_35 ),
    inference(resolution,[],[f453,f337])).

fof(f337,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl5_35
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f453,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f454,plain,
    ( spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f451,f442,f121,f117,f106])).

fof(f117,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f121,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f442,plain,
    ( spl5_44
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_44 ),
    inference(resolution,[],[f448,f118])).

fof(f118,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl5_7
    | ~ spl5_44 ),
    inference(resolution,[],[f443,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f443,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( ~ spl5_17
    | spl5_44
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f440,f247,f218,f442,f215])).

fof(f218,plain,
    ( spl5_18
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f247,plain,
    ( spl5_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f440,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f438,f248])).

fof(f248,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f247])).

fof(f438,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_18 ),
    inference(resolution,[],[f340,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f80,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f340,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_relat_1(sK3),X3)
        | ~ r1_tarski(X3,X2)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) )
    | ~ spl5_18 ),
    inference(resolution,[],[f219,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f381,plain,
    ( ~ spl5_17
    | ~ spl5_22
    | spl5_38 ),
    inference(avatar_split_clause,[],[f380,f373,f256,f215])).

fof(f380,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK3)
    | spl5_38 ),
    inference(forward_demodulation,[],[f378,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f378,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | ~ v1_relat_1(sK3) )
    | spl5_38 ),
    inference(resolution,[],[f374,f185])).

fof(f374,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f373])).

fof(f357,plain,
    ( ~ spl5_22
    | spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f356,f113,f106,f256])).

fof(f113,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f356,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f352,f89])).

fof(f352,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f107,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f107,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f338,plain,
    ( ~ spl5_17
    | spl5_35
    | spl5_34 ),
    inference(avatar_split_clause,[],[f333,f330,f336,f215])).

fof(f330,plain,
    ( spl5_34
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_relat_1(sK3) )
    | spl5_34 ),
    inference(resolution,[],[f331,f185])).

fof(f331,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f330])).

fof(f332,plain,
    ( ~ spl5_34
    | spl5_2
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f328,f291,f103,f330])).

fof(f103,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f291,plain,
    ( spl5_28
  <=> ! [X0] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f328,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_2
    | ~ spl5_28 ),
    inference(resolution,[],[f292,f104])).

fof(f104,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f292,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f291])).

fof(f321,plain,
    ( ~ spl5_33
    | ~ spl5_22
    | spl5_24 ),
    inference(avatar_split_clause,[],[f315,f265,f256,f318])).

fof(f265,plain,
    ( spl5_24
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | spl5_24 ),
    inference(resolution,[],[f266,f151])).

fof(f151,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f97,f89])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f266,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f265])).

fof(f312,plain,
    ( spl5_32
    | spl5_27
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f308,f256,f286,f310])).

fof(f286,plain,
    ( spl5_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f308,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK3
        | ~ v1_funct_2(sK3,X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl5_22 ),
    inference(resolution,[],[f257,f150])).

fof(f150,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f96,f88])).

fof(f96,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f257,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f256])).

fof(f293,plain,
    ( ~ spl5_17
    | ~ spl5_1
    | spl5_28
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f268,f247,f291,f100,f215])).

fof(f268,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_21 ),
    inference(superposition,[],[f66,f248])).

fof(f280,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl5_25 ),
    inference(resolution,[],[f275,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f275,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl5_25
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f276,plain,
    ( ~ spl5_25
    | ~ spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f272,f215,f121,f274])).

fof(f272,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_7
    | spl5_17 ),
    inference(resolution,[],[f237,f122])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_17 ),
    inference(resolution,[],[f216,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f216,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f267,plain,
    ( ~ spl5_24
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f253,f113,f103,f265])).

fof(f253,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f104,f114])).

fof(f258,plain,
    ( spl5_22
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f254,f121,f113,f256])).

fof(f254,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f251,f89])).

fof(f251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f122,f114])).

fof(f250,plain,
    ( ~ spl5_7
    | spl5_21
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f244,f232,f247,f121])).

fof(f232,plain,
    ( spl5_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f244,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_19 ),
    inference(superposition,[],[f79,f233])).

fof(f233,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f236,plain,
    ( spl5_19
    | spl5_4
    | ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f227,f121,f125,f110,f232])).

fof(f110,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f125,plain,
    ( spl5_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f227,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f81,f122])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f220,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f210,f100,f218,f215])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f128])).

fof(f128,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f54,f139])).

fof(f139,plain,
    ( spl5_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f129,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f127,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f48,f125])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f123,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f51,f113,f110])).

fof(f51,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f52,f106,f103,f100])).

fof(f52,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21120)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (21128)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (21122)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (21108)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (21114)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (21126)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (21108)Refutation not found, incomplete strategy% (21108)------------------------------
% 0.21/0.48  % (21108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21108)Memory used [KB]: 6140
% 0.21/0.48  % (21108)Time elapsed: 0.072 s
% 0.21/0.48  % (21108)------------------------------
% 0.21/0.48  % (21108)------------------------------
% 0.21/0.48  % (21114)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f528,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f108,f115,f119,f123,f127,f129,f141,f220,f236,f250,f258,f267,f276,f280,f293,f312,f321,f332,f338,f357,f381,f444,f454,f468,f485,f488,f527])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f488,plain,(
% 0.21/0.48    ~spl5_48 | ~spl5_22 | spl5_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f486,f318,f256,f483])).
% 0.21/0.48  fof(f483,plain,(
% 0.21/0.48    spl5_48 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    spl5_22 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    spl5_33 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.48  fof(f486,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(sK3) | spl5_33),
% 0.21/0.48    inference(forward_demodulation,[],[f365,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | spl5_33),
% 0.21/0.48    inference(superposition,[],[f319,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | spl5_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f318])).
% 0.21/0.48  fof(f485,plain,(
% 0.21/0.48    ~spl5_17 | ~spl5_1 | ~spl5_38 | spl5_48 | ~spl5_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f369,f310,f483,f373,f100,f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl5_17 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    spl5_38 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    spl5_32 <=> ! [X1] : (~v1_funct_2(sK3,X1,k1_xboole_0) | k1_xboole_0 = X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_32),
% 0.21/0.48    inference(resolution,[],[f311,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_2(sK3,X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl5_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f310])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    ~spl5_3 | ~spl5_35),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f461])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    $false | (~spl5_3 | ~spl5_35)),
% 0.21/0.48    inference(resolution,[],[f453,f337])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_35),
% 0.21/0.48    inference(avatar_component_clause,[],[f336])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    spl5_35 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f454,plain,(
% 0.21/0.48    spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f451,f442,f121,f117,f106])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl5_6 <=> r1_tarski(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f442,plain,(
% 0.21/0.48    spl5_44 <=> ! [X1,X0,X2] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.48  fof(f451,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_6 | ~spl5_7 | ~spl5_44)),
% 0.21/0.48    inference(resolution,[],[f448,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f448,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (~spl5_7 | ~spl5_44)),
% 0.21/0.48    inference(resolution,[],[f443,f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f443,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r1_tarski(X0,X1)) ) | ~spl5_44),
% 0.21/0.48    inference(avatar_component_clause,[],[f442])).
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    ~spl5_17 | spl5_44 | ~spl5_18 | ~spl5_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f440,f247,f218,f442,f215])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl5_18 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    spl5_21 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r1_tarski(X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(sK3)) ) | (~spl5_18 | ~spl5_21)),
% 0.21/0.48    inference(forward_demodulation,[],[f438,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl5_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f247])).
% 0.21/0.48  fof(f438,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(sK3)) ) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f340,f185])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f80,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(sK3),X3) | ~r1_tarski(X3,X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))) ) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f219,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) ) | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    ~spl5_17 | ~spl5_22 | spl5_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f380,f373,f256,f215])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK3) | spl5_38),
% 0.21/0.48    inference(forward_demodulation,[],[f378,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_relat_1(sK3)) ) | spl5_38),
% 0.21/0.48    inference(resolution,[],[f374,f185])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl5_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f373])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    ~spl5_22 | spl5_3 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f356,f113,f106,f256])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl5_5 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f352,f89])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl5_3 | ~spl5_5)),
% 0.21/0.48    inference(superposition,[],[f107,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    ~spl5_17 | spl5_35 | spl5_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f333,f330,f336,f215])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    spl5_34 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_relat_1(sK3)) ) | spl5_34),
% 0.21/0.48    inference(resolution,[],[f331,f185])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK2) | spl5_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f330])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    ~spl5_34 | spl5_2 | ~spl5_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f328,f291,f103,f330])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl5_28 <=> ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK2) | (spl5_2 | ~spl5_28)),
% 0.21/0.48    inference(resolution,[],[f292,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK2) | spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl5_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f291])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    ~spl5_33 | ~spl5_22 | spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f315,f265,f256,f318])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl5_24 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | spl5_24),
% 0.21/0.48    inference(resolution,[],[f266,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f97,f89])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f265])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    spl5_32 | spl5_27 | ~spl5_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f308,f256,f286,f310])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    spl5_27 <=> k1_xboole_0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = sK3 | ~v1_funct_2(sK3,X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl5_22),
% 0.21/0.48    inference(resolution,[],[f257,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f96,f88])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f256])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    ~spl5_17 | ~spl5_1 | spl5_28 | ~spl5_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f268,f247,f291,f100,f215])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_21),
% 0.21/0.48    inference(superposition,[],[f66,f248])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    spl5_25),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    $false | spl5_25),
% 0.21/0.48    inference(resolution,[],[f275,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f274])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    spl5_25 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~spl5_25 | ~spl5_7 | spl5_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f272,f215,f121,f274])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_7 | spl5_17)),
% 0.21/0.48    inference(resolution,[],[f237,f122])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_17),
% 0.21/0.48    inference(resolution,[],[f216,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | spl5_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~spl5_24 | spl5_2 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f253,f113,f103,f265])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl5_2 | ~spl5_5)),
% 0.21/0.48    inference(superposition,[],[f104,f114])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl5_22 | ~spl5_5 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f254,f121,f113,f256])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_5 | ~spl5_7)),
% 0.21/0.48    inference(forward_demodulation,[],[f251,f89])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_5 | ~spl5_7)),
% 0.21/0.48    inference(superposition,[],[f122,f114])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ~spl5_7 | spl5_21 | ~spl5_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f244,f232,f247,f121])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    spl5_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_19),
% 0.21/0.48    inference(superposition,[],[f79,f233])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f232])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    spl5_19 | spl5_4 | ~spl5_8 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f227,f121,f125,f110,f232])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl5_4 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl5_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f81,f122])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~spl5_17 | spl5_18 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f210,f100,f218,f215])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f67,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl5_11 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f100])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f125])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f121])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f117])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~spl5_4 | spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f113,f110])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f106,f103,f100])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21114)------------------------------
% 0.21/0.48  % (21114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21114)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21114)Memory used [KB]: 10874
% 0.21/0.48  % (21114)Time elapsed: 0.015 s
% 0.21/0.48  % (21114)------------------------------
% 0.21/0.48  % (21114)------------------------------
% 0.21/0.48  % (21107)Success in time 0.128 s
%------------------------------------------------------------------------------
