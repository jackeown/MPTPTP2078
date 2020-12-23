%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 344 expanded)
%              Number of leaves         :   54 ( 169 expanded)
%              Depth                    :    8
%              Number of atoms          :  618 (1645 expanded)
%              Number of equality atoms :  173 ( 492 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f104,f109,f114,f132,f137,f142,f148,f154,f160,f177,f184,f198,f205,f227,f238,f278,f285,f291,f299,f312,f455,f457,f503,f530,f539,f545,f551,f552])).

fof(f552,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f551,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f545,plain,
    ( spl3_68
    | ~ spl3_14
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f540,f451,f134,f542])).

fof(f542,plain,
    ( spl3_68
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f134,plain,
    ( spl3_14
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f451,plain,
    ( spl3_59
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f540,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f532,f136])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f532,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_59 ),
    inference(resolution,[],[f453,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f453,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f451])).

fof(f539,plain,
    ( spl3_67
    | ~ spl3_15
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f534,f451,f139,f536])).

fof(f536,plain,
    ( spl3_67
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f139,plain,
    ( spl3_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f534,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_15
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f531,f141])).

fof(f141,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f531,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_59 ),
    inference(resolution,[],[f453,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f530,plain,
    ( ~ spl3_7
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_3
    | spl3_59
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f521,f489,f451,f76,f441,f437,f96])).

fof(f96,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f437,plain,
    ( spl3_56
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

% (6773)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f441,plain,
    ( spl3_57
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f76,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f489,plain,
    ( spl3_64
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f521,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_64 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_64 ),
    inference(superposition,[],[f62,f491])).

fof(f491,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f489])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f503,plain,
    ( spl3_64
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f500,f441,f489])).

fof(f500,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_57 ),
    inference(resolution,[],[f442,f59])).

fof(f442,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f441])).

fof(f457,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f455,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f312,plain,
    ( spl3_40
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f306,f296,f308])).

fof(f308,plain,
    ( spl3_40
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f296,plain,
    ( spl3_38
  <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f306,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_38 ),
    inference(superposition,[],[f50,f298])).

fof(f298,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f296])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f299,plain,
    ( spl3_38
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f293,f224,f129,f296])).

fof(f129,plain,
    ( spl3_13
  <=> k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f224,plain,
    ( spl3_27
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f293,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0)))
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f131,f226])).

fof(f226,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f131,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f291,plain,
    ( spl3_23
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f288,f181,f189])).

fof(f189,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f181,plain,
    ( spl3_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f288,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_22 ),
    inference(resolution,[],[f183,f59])).

fof(f183,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f285,plain,(
    spl3_36 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl3_36 ),
    inference(resolution,[],[f277,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f277,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_36
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f278,plain,
    ( ~ spl3_36
    | spl3_18
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f257,f220,f157,f275])).

fof(f157,plain,
    ( spl3_18
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f220,plain,
    ( spl3_26
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f257,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_18
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f159,f222])).

fof(f222,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f220])).

fof(f159,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f238,plain,
    ( ~ spl3_7
    | ~ spl3_21
    | ~ spl3_22
    | spl3_29
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f215,f202,f76,f235,f181,f174,f96])).

fof(f174,plain,
    ( spl3_21
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f235,plain,
    ( spl3_29
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f202,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f215,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25 ),
    inference(superposition,[],[f63,f204])).

fof(f204,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f227,plain,
    ( ~ spl3_7
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_3
    | spl3_26
    | spl3_27
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f218,f202,f224,f220,f76,f181,f174,f96])).

fof(f218,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f217,f48])).

fof(f48,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f217,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f206])).

fof(f206,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25 ),
    inference(superposition,[],[f64,f204])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f205,plain,
    ( spl3_25
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f200,f151,f145,f81,f202])).

fof(f81,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( spl3_16
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f151,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f200,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f199,f153])).

fof(f153,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f199,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f83,f147])).

fof(f147,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f83,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f198,plain,
    ( spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f187,f181,f120])).

fof(f120,plain,
    ( spl3_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f187,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_22 ),
    inference(resolution,[],[f183,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f184,plain,
    ( spl3_22
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f179,f151,f145,f86,f181])).

fof(f86,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f179,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f178,f153])).

fof(f178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f88,f147])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f177,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f172,f151,f145,f91,f174])).

fof(f91,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

% (6766)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (6761)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% (6765)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (6767)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (6771)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (6775)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f172,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f171,f153])).

fof(f171,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f93,f147])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f160,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f155,f145,f157,f101,f106])).

fof(f106,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f101,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f155,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f147])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f154,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f149,f111,f151])).

fof(f111,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f149,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f148,plain,
    ( spl3_16
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f143,f101,f145])).

fof(f143,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f103,f51])).

fof(f103,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f142,plain,
    ( ~ spl3_11
    | ~ spl3_7
    | spl3_15
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f118,f76,f139,f96,f120])).

fof(f118,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f78,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f137,plain,
    ( ~ spl3_11
    | ~ spl3_7
    | spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f117,f76,f134,f96,f120])).

fof(f117,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,
    ( ~ spl3_11
    | ~ spl3_7
    | spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f116,f76,f129,f96,f120])).

fof(f116,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f114,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f111])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f109,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f39,f106])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f43,f86])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f81])).

fof(f44,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f71,f67])).

fof(f67,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (6762)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (6759)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (6768)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (6758)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (6774)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (6764)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (6769)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (6763)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (6772)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (6760)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (6769)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f553,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f104,f109,f114,f132,f137,f142,f148,f154,f160,f177,f184,f198,f205,f227,f238,f278,f285,f291,f299,f312,f455,f457,f503,f530,f539,f545,f551,f552])).
% 0.20/0.49  fof(f552,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f551,plain,(
% 0.20/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f545,plain,(
% 0.20/0.49    spl3_68 | ~spl3_14 | ~spl3_59),
% 0.20/0.49    inference(avatar_split_clause,[],[f540,f451,f134,f542])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    spl3_68 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl3_14 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f451,plain,(
% 0.20/0.49    spl3_59 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.49  fof(f540,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_14 | ~spl3_59)),
% 0.20/0.49    inference(forward_demodulation,[],[f532,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f532,plain,(
% 0.20/0.49    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_59),
% 0.20/0.49    inference(resolution,[],[f453,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_59),
% 0.20/0.49    inference(avatar_component_clause,[],[f451])).
% 0.20/0.49  fof(f539,plain,(
% 0.20/0.49    spl3_67 | ~spl3_15 | ~spl3_59),
% 0.20/0.49    inference(avatar_split_clause,[],[f534,f451,f139,f536])).
% 0.20/0.49  fof(f536,plain,(
% 0.20/0.49    spl3_67 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl3_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f534,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_15 | ~spl3_59)),
% 0.20/0.49    inference(forward_demodulation,[],[f531,f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f139])).
% 0.20/0.49  fof(f531,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_59),
% 0.20/0.49    inference(resolution,[],[f453,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f530,plain,(
% 0.20/0.49    ~spl3_7 | ~spl3_56 | ~spl3_57 | ~spl3_3 | spl3_59 | ~spl3_64),
% 0.20/0.49    inference(avatar_split_clause,[],[f521,f489,f451,f76,f441,f437,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl3_7 <=> v1_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f437,plain,(
% 0.20/0.49    spl3_56 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.49  % (6773)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  fof(f441,plain,(
% 0.20/0.49    spl3_57 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_3 <=> v2_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    spl3_64 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.20/0.49  fof(f521,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_64),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f520])).
% 0.20/0.49  fof(f520,plain,(
% 0.20/0.49    k2_relat_1(sK2) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_64),
% 0.20/0.49    inference(superposition,[],[f62,f491])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_64),
% 0.20/0.49    inference(avatar_component_clause,[],[f489])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.49  fof(f503,plain,(
% 0.20/0.49    spl3_64 | ~spl3_57),
% 0.20/0.49    inference(avatar_split_clause,[],[f500,f441,f489])).
% 0.20/0.49  fof(f500,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_57),
% 0.20/0.49    inference(resolution,[],[f442,f59])).
% 0.20/0.49  fof(f442,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_57),
% 0.20/0.49    inference(avatar_component_clause,[],[f441])).
% 0.20/0.49  fof(f457,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f455,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    spl3_40 | ~spl3_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f306,f296,f308])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    spl3_40 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    spl3_38 <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.49  fof(f306,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_38),
% 0.20/0.49    inference(superposition,[],[f50,f298])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0))) | ~spl3_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f296])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    spl3_38 | ~spl3_13 | ~spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f293,f224,f129,f296])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl3_13 <=> k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    spl3_27 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_struct_0(sK0))) | (~spl3_13 | ~spl3_27)),
% 0.20/0.49    inference(backward_demodulation,[],[f131,f226])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f224])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    spl3_23 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f288,f181,f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    spl3_23 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    spl3_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_22),
% 0.20/0.49    inference(resolution,[],[f183,f59])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f181])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    spl3_36),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    $false | spl3_36),
% 0.20/0.49    inference(resolution,[],[f277,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | spl3_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f275])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    spl3_36 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    ~spl3_36 | spl3_18 | ~spl3_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f257,f220,f157,f275])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl3_18 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    spl3_26 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | (spl3_18 | ~spl3_26)),
% 0.20/0.49    inference(backward_demodulation,[],[f159,f222])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f220])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    ~spl3_7 | ~spl3_21 | ~spl3_22 | spl3_29 | ~spl3_3 | ~spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f215,f202,f76,f235,f181,f174,f96])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl3_21 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    spl3_29 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    spl3_25 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_25),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f208])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_25),
% 0.20/0.49    inference(superposition,[],[f63,f204])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f202])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    ~spl3_7 | ~spl3_21 | ~spl3_22 | ~spl3_3 | spl3_26 | spl3_27 | ~spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f218,f202,f224,f220,f76,f181,f174,f96])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_25),
% 0.20/0.49    inference(forward_demodulation,[],[f217,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_25),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f206])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_25),
% 0.20/0.49    inference(superposition,[],[f64,f204])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    spl3_25 | ~spl3_4 | ~spl3_16 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f200,f151,f145,f81,f202])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl3_16 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl3_17 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_16 | ~spl3_17)),
% 0.20/0.49    inference(forward_demodulation,[],[f199,f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f151])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f83,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f145])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    spl3_11 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f187,f181,f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl3_11 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_22),
% 0.20/0.49    inference(resolution,[],[f183,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl3_22 | ~spl3_5 | ~spl3_16 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f179,f151,f145,f86,f181])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_16 | ~spl3_17)),
% 0.20/0.49    inference(forward_demodulation,[],[f178,f153])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f88,f147])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    spl3_21 | ~spl3_6 | ~spl3_16 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f172,f151,f145,f91,f174])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  % (6766)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (6761)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (6765)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (6767)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (6771)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (6775)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_16 | ~spl3_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f171,f153])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f93,f147])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f91])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_18 | ~spl3_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f155,f145,f157,f101,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl3_9 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl3_8 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_16),
% 0.20/0.50    inference(superposition,[],[f52,f147])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl3_17 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f149,f111,f151])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_10 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(resolution,[],[f113,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl3_16 | ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f143,f101,f145])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.20/0.50    inference(resolution,[],[f103,f51])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    l1_struct_0(sK1) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~spl3_11 | ~spl3_7 | spl3_15 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f118,f76,f139,f96,f120])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f78,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~spl3_11 | ~spl3_7 | spl3_14 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f117,f76,f134,f96,f120])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f78,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ~spl3_11 | ~spl3_7 | spl3_13 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f116,f76,f129,f96,f120])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f78,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f111])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f36,f35,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f106])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f101])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f96])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f91])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f86])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f81])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f76])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f71,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (6769)------------------------------
% 0.20/0.50  % (6769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6769)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (6769)Memory used [KB]: 11001
% 0.20/0.50  % (6769)Time elapsed: 0.066 s
% 0.20/0.50  % (6769)------------------------------
% 0.20/0.50  % (6769)------------------------------
% 0.20/0.50  % (6770)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (6757)Success in time 0.137 s
%------------------------------------------------------------------------------
