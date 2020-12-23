%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:00 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 476 expanded)
%              Number of leaves         :   68 ( 231 expanded)
%              Depth                    :    8
%              Number of atoms          :  885 (2059 expanded)
%              Number of equality atoms :  219 ( 576 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f666,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f146,f156,f160,f174,f179,f184,f199,f209,f223,f241,f280,f285,f293,f307,f310,f311,f347,f364,f386,f400,f401,f425,f459,f465,f492,f496,f515,f541,f560,f565,f569,f657,f663,f664])).

fof(f664,plain,
    ( k1_xboole_0 != sK2
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f663,plain,
    ( spl3_73
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f659,f655,f661])).

fof(f661,plain,
    ( spl3_73
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f655,plain,
    ( spl3_72
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f659,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_72 ),
    inference(resolution,[],[f656,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f656,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f655])).

fof(f657,plain,
    ( spl3_72
    | ~ spl3_11
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f650,f539,f133,f655])).

fof(f133,plain,
    ( spl3_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f539,plain,
    ( spl3_66
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f650,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_11
    | ~ spl3_66 ),
    inference(resolution,[],[f540,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl3_11 ),
    inference(resolution,[],[f66,f134])).

fof(f134,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f540,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f539])).

fof(f569,plain,
    ( ~ spl3_32
    | ~ spl3_7
    | ~ spl3_3
    | spl3_69 ),
    inference(avatar_split_clause,[],[f568,f563,f101,f117,f275])).

fof(f275,plain,
    ( spl3_32
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f117,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f563,plain,
    ( spl3_69
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f568,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_69 ),
    inference(trivial_inequality_removal,[],[f567])).

fof(f567,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_69 ),
    inference(superposition,[],[f564,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f564,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_69 ),
    inference(avatar_component_clause,[],[f563])).

fof(f565,plain,
    ( ~ spl3_69
    | ~ spl3_50
    | spl3_68 ),
    inference(avatar_split_clause,[],[f561,f558,f423,f563])).

fof(f423,plain,
    ( spl3_50
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f558,plain,
    ( spl3_68
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f561,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_50
    | spl3_68 ),
    inference(superposition,[],[f559,f424])).

fof(f424,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f423])).

fof(f559,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_68 ),
    inference(avatar_component_clause,[],[f558])).

fof(f560,plain,
    ( ~ spl3_68
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_23
    | ~ spl3_35
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f556,f487,f302,f212,f158,f154,f97,f558])).

fof(f97,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f154,plain,
    ( spl3_15
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f158,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f212,plain,
    ( spl3_23
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f302,plain,
    ( spl3_35
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f487,plain,
    ( spl3_56
  <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f556,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_23
    | ~ spl3_35
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f555,f488])).

fof(f488,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f487])).

fof(f555,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f554,f303])).

fof(f303,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f302])).

fof(f554,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f553,f159])).

fof(f159,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f553,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f552,f213])).

fof(f213,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f552,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f98,f155])).

fof(f155,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f98,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f541,plain,
    ( spl3_66
    | ~ spl3_42
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f526,f409,f362,f539])).

fof(f362,plain,
    ( spl3_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f409,plain,
    ( spl3_46
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f526,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | ~ spl3_42
    | ~ spl3_46 ),
    inference(superposition,[],[f363,f410])).

fof(f410,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f409])).

fof(f363,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f362])).

fof(f515,plain,
    ( spl3_45
    | spl3_46
    | ~ spl3_47
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f469,f395,f412,f409,f406])).

fof(f406,plain,
    ( spl3_45
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f412,plain,
    ( spl3_47
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f395,plain,
    ( spl3_44
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f469,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(resolution,[],[f396,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f396,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f395])).

fof(f496,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f492,plain,
    ( spl3_56
    | ~ spl3_40
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f491,f457,f362,f314,f342,f487])).

fof(f342,plain,
    ( spl3_40
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f314,plain,
    ( spl3_37
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f457,plain,
    ( spl3_55
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f491,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(trivial_inequality_removal,[],[f490])).

fof(f490,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f480,f315])).

fof(f315,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f314])).

fof(f480,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(resolution,[],[f458,f363])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f457])).

fof(f465,plain,
    ( ~ spl3_7
    | ~ spl3_40
    | ~ spl3_42
    | ~ spl3_3
    | ~ spl3_37
    | spl3_47 ),
    inference(avatar_split_clause,[],[f463,f412,f314,f101,f362,f342,f117])).

fof(f463,plain,
    ( ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_37
    | spl3_47 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_37
    | spl3_47 ),
    inference(forward_demodulation,[],[f460,f315])).

fof(f460,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_47 ),
    inference(resolution,[],[f413,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f413,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f412])).

fof(f459,plain,
    ( ~ spl3_7
    | spl3_55
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f455,f101,f457,f117])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f102])).

fof(f102,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

% (28533)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f425,plain,
    ( spl3_50
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f404,f395,f423])).

fof(f404,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(resolution,[],[f396,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f401,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f400,plain,
    ( spl3_44
    | ~ spl3_40
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f399,f384,f362,f314,f342,f395])).

fof(f384,plain,
    ( spl3_43
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f399,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_37
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f388,f315])).

fof(f388,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(resolution,[],[f385,f363])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f384])).

fof(f386,plain,
    ( ~ spl3_7
    | spl3_43
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f381,f101,f384,f117])).

fof(f381,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f80,f102])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f364,plain,
    ( spl3_42
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f352,f302,f235,f362])).

fof(f235,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(superposition,[],[f236,f303])).

fof(f236,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f235])).

fof(f347,plain,
    ( spl3_40
    | ~ spl3_28
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f333,f302,f239,f342])).

fof(f239,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f333,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_28
    | ~ spl3_35 ),
    inference(superposition,[],[f240,f303])).

fof(f240,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f311,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f310,plain,
    ( ~ spl3_27
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl3_27
    | spl3_36 ),
    inference(subsumption_resolution,[],[f236,f308])).

fof(f308,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_36 ),
    inference(resolution,[],[f306,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f306,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl3_36
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f307,plain,
    ( ~ spl3_28
    | spl3_34
    | spl3_35
    | ~ spl3_36
    | ~ spl3_27
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f296,f278,f235,f305,f302,f299,f239])).

fof(f299,plain,
    ( spl3_34
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f278,plain,
    ( spl3_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f296,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_27
    | ~ spl3_33 ),
    inference(resolution,[],[f279,f236])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f293,plain,
    ( spl3_27
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f292,f212,f177,f235])).

fof(f177,plain,
    ( spl3_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f292,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f178,f213])).

fof(f178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f285,plain,
    ( ~ spl3_5
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl3_5
    | spl3_32 ),
    inference(subsumption_resolution,[],[f110,f281])).

fof(f281,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_32 ),
    inference(resolution,[],[f276,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f276,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f275])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f280,plain,
    ( ~ spl3_32
    | spl3_33
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f273,f117,f278,f275])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(resolution,[],[f272,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f272,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f91,f118])).

fof(f118,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f241,plain,
    ( spl3_28
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f227,f212,f182,f239])).

fof(f182,plain,
    ( spl3_20
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f227,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(superposition,[],[f183,f213])).

fof(f183,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f223,plain,
    ( spl3_23
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f221,f207,f162,f212])).

fof(f162,plain,
    ( spl3_17
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f207,plain,
    ( spl3_22
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f221,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(superposition,[],[f163,f208])).

fof(f208,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f163,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f209,plain,
    ( spl3_22
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f205,f158,f154,f109,f207])).

fof(f205,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f204,f159])).

fof(f204,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f202,f155])).

fof(f202,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f70,f110])).

fof(f199,plain,
    ( ~ spl3_8
    | ~ spl3_21
    | spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f194,f154,f125,f197,f121])).

fof(f121,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f197,plain,
    ( spl3_21
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f125,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f194,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f193,f155])).

fof(f193,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_9 ),
    inference(resolution,[],[f63,f126])).

fof(f126,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f63,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f184,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f180,f158,f154,f113,f182])).

fof(f113,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f180,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f167,f159])).

fof(f167,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f114,f155])).

fof(f114,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f179,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f175,f158,f154,f109,f177])).

fof(f175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f166,f159])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(superposition,[],[f110,f155])).

fof(f174,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f173,f158,f154,f105,f162])).

fof(f105,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f173,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f165,f159])).

fof(f165,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(superposition,[],[f106,f155])).

fof(f106,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f160,plain,
    ( spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f152,f129,f158])).

fof(f129,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f152,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f61,f130])).

fof(f130,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f156,plain,
    ( spl3_15
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f151,f121,f154])).

fof(f151,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f122])).

fof(f122,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f146,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f141,f137,f144])).

fof(f144,plain,
    ( spl3_13
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f137,plain,
    ( spl3_12
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

% (28540)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f141,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f60,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f139,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f135,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f127,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f49,f125])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f121])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f119,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f54,f105])).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f97,f94])).

fof(f94,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n015.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:26:08 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.41  % (28544)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.17/0.42  % (28536)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.42  % (28544)Refutation not found, incomplete strategy% (28544)------------------------------
% 0.17/0.42  % (28544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.42  % (28544)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.42  
% 0.17/0.42  % (28544)Memory used [KB]: 1663
% 0.17/0.42  % (28544)Time elapsed: 0.054 s
% 0.17/0.42  % (28544)------------------------------
% 0.17/0.42  % (28544)------------------------------
% 0.17/0.42  % (28543)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.42  % (28543)Refutation not found, incomplete strategy% (28543)------------------------------
% 0.17/0.42  % (28543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.42  % (28543)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.42  
% 0.17/0.42  % (28543)Memory used [KB]: 6140
% 0.17/0.42  % (28543)Time elapsed: 0.061 s
% 0.17/0.42  % (28543)------------------------------
% 0.17/0.42  % (28543)------------------------------
% 0.17/0.43  % (28538)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.17/0.43  % (28537)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.17/0.43  % (28551)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.17/0.44  % (28551)Refutation not found, incomplete strategy% (28551)------------------------------
% 0.17/0.44  % (28551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.44  % (28551)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.44  
% 0.17/0.44  % (28551)Memory used [KB]: 10618
% 0.17/0.44  % (28551)Time elapsed: 0.072 s
% 0.17/0.44  % (28551)------------------------------
% 0.17/0.44  % (28551)------------------------------
% 0.17/0.44  % (28535)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.17/0.44  % (28546)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.17/0.44  % (28545)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.17/0.45  % (28532)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.45  % (28537)Refutation found. Thanks to Tanya!
% 0.17/0.45  % SZS status Theorem for theBenchmark
% 0.17/0.45  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f666,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(avatar_sat_refutation,[],[f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f146,f156,f160,f174,f179,f184,f199,f209,f223,f241,f280,f285,f293,f307,f310,f311,f347,f364,f386,f400,f401,f425,f459,f465,f492,f496,f515,f541,f560,f565,f569,f657,f663,f664])).
% 0.17/0.45  fof(f664,plain,(
% 0.17/0.45    k1_xboole_0 != sK2 | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 0.17/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.17/0.45  fof(f663,plain,(
% 0.17/0.45    spl3_73 | ~spl3_72),
% 0.17/0.45    inference(avatar_split_clause,[],[f659,f655,f661])).
% 0.17/0.45  fof(f661,plain,(
% 0.17/0.45    spl3_73 <=> k1_xboole_0 = sK2),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.17/0.45  fof(f655,plain,(
% 0.17/0.45    spl3_72 <=> v1_xboole_0(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.17/0.45  fof(f659,plain,(
% 0.17/0.45    k1_xboole_0 = sK2 | ~spl3_72),
% 0.17/0.45    inference(resolution,[],[f656,f62])).
% 0.17/0.45  fof(f62,plain,(
% 0.17/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.17/0.45    inference(cnf_transformation,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f2])).
% 0.17/0.45  fof(f2,axiom,(
% 0.17/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.17/0.45  fof(f656,plain,(
% 0.17/0.45    v1_xboole_0(sK2) | ~spl3_72),
% 0.17/0.45    inference(avatar_component_clause,[],[f655])).
% 0.17/0.45  fof(f657,plain,(
% 0.17/0.45    spl3_72 | ~spl3_11 | ~spl3_66),
% 0.17/0.45    inference(avatar_split_clause,[],[f650,f539,f133,f655])).
% 0.17/0.45  fof(f133,plain,(
% 0.17/0.45    spl3_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.17/0.45  fof(f539,plain,(
% 0.17/0.45    spl3_66 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.17/0.45  fof(f650,plain,(
% 0.17/0.45    v1_xboole_0(sK2) | (~spl3_11 | ~spl3_66)),
% 0.17/0.45    inference(resolution,[],[f540,f200])).
% 0.17/0.45  fof(f200,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl3_11),
% 0.17/0.45    inference(resolution,[],[f66,f134])).
% 0.17/0.45  fof(f134,plain,(
% 0.17/0.45    v1_xboole_0(k1_xboole_0) | ~spl3_11),
% 0.17/0.45    inference(avatar_component_clause,[],[f133])).
% 0.17/0.45  fof(f66,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,axiom,(
% 0.17/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.17/0.45  fof(f540,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | ~spl3_66),
% 0.17/0.45    inference(avatar_component_clause,[],[f539])).
% 0.17/0.45  fof(f569,plain,(
% 0.17/0.45    ~spl3_32 | ~spl3_7 | ~spl3_3 | spl3_69),
% 0.17/0.45    inference(avatar_split_clause,[],[f568,f563,f101,f117,f275])).
% 0.17/0.45  fof(f275,plain,(
% 0.17/0.45    spl3_32 <=> v1_relat_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.17/0.45  fof(f117,plain,(
% 0.17/0.45    spl3_7 <=> v1_funct_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.17/0.45  fof(f101,plain,(
% 0.17/0.45    spl3_3 <=> v2_funct_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.45  fof(f563,plain,(
% 0.17/0.45    spl3_69 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.17/0.45  fof(f568,plain,(
% 0.17/0.45    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_69),
% 0.17/0.45    inference(trivial_inequality_removal,[],[f567])).
% 0.17/0.45  fof(f567,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_69),
% 0.17/0.45    inference(superposition,[],[f564,f65])).
% 0.17/0.45  fof(f65,plain,(
% 0.17/0.45    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f27])).
% 0.17/0.45  fof(f27,plain,(
% 0.17/0.45    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.17/0.45  fof(f564,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_69),
% 0.17/0.45    inference(avatar_component_clause,[],[f563])).
% 0.17/0.45  fof(f565,plain,(
% 0.17/0.45    ~spl3_69 | ~spl3_50 | spl3_68),
% 0.17/0.45    inference(avatar_split_clause,[],[f561,f558,f423,f563])).
% 0.17/0.45  fof(f423,plain,(
% 0.17/0.45    spl3_50 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.17/0.45  fof(f558,plain,(
% 0.17/0.45    spl3_68 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.17/0.45  fof(f561,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_50 | spl3_68)),
% 0.17/0.45    inference(superposition,[],[f559,f424])).
% 0.17/0.45  fof(f424,plain,(
% 0.17/0.45    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_50),
% 0.17/0.45    inference(avatar_component_clause,[],[f423])).
% 0.17/0.45  fof(f559,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_68),
% 0.17/0.45    inference(avatar_component_clause,[],[f558])).
% 0.17/0.45  fof(f560,plain,(
% 0.17/0.45    ~spl3_68 | spl3_2 | ~spl3_15 | ~spl3_16 | ~spl3_23 | ~spl3_35 | ~spl3_56),
% 0.17/0.45    inference(avatar_split_clause,[],[f556,f487,f302,f212,f158,f154,f97,f558])).
% 0.17/0.45  fof(f97,plain,(
% 0.17/0.45    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.45  fof(f154,plain,(
% 0.17/0.45    spl3_15 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.17/0.45  fof(f158,plain,(
% 0.17/0.45    spl3_16 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.17/0.45  fof(f212,plain,(
% 0.17/0.45    spl3_23 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.17/0.45  fof(f302,plain,(
% 0.17/0.45    spl3_35 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.17/0.45  fof(f487,plain,(
% 0.17/0.45    spl3_56 <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.17/0.45  fof(f556,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_2 | ~spl3_15 | ~spl3_16 | ~spl3_23 | ~spl3_35 | ~spl3_56)),
% 0.17/0.45    inference(forward_demodulation,[],[f555,f488])).
% 0.17/0.45  fof(f488,plain,(
% 0.17/0.45    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~spl3_56),
% 0.17/0.45    inference(avatar_component_clause,[],[f487])).
% 0.17/0.45  fof(f555,plain,(
% 0.17/0.45    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_15 | ~spl3_16 | ~spl3_23 | ~spl3_35)),
% 0.17/0.45    inference(forward_demodulation,[],[f554,f303])).
% 0.17/0.45  fof(f303,plain,(
% 0.17/0.45    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_35),
% 0.17/0.45    inference(avatar_component_clause,[],[f302])).
% 0.17/0.45  fof(f554,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_15 | ~spl3_16 | ~spl3_23)),
% 0.17/0.45    inference(forward_demodulation,[],[f553,f159])).
% 0.17/0.45  fof(f159,plain,(
% 0.17/0.45    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_16),
% 0.17/0.45    inference(avatar_component_clause,[],[f158])).
% 0.17/0.45  fof(f553,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_15 | ~spl3_23)),
% 0.17/0.45    inference(forward_demodulation,[],[f552,f213])).
% 0.17/0.45  fof(f213,plain,(
% 0.17/0.45    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_23),
% 0.17/0.45    inference(avatar_component_clause,[],[f212])).
% 0.17/0.45  fof(f552,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_15)),
% 0.17/0.45    inference(forward_demodulation,[],[f98,f155])).
% 0.17/0.45  fof(f155,plain,(
% 0.17/0.45    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_15),
% 0.17/0.45    inference(avatar_component_clause,[],[f154])).
% 0.17/0.45  fof(f98,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.17/0.45    inference(avatar_component_clause,[],[f97])).
% 0.17/0.45  fof(f541,plain,(
% 0.17/0.45    spl3_66 | ~spl3_42 | ~spl3_46),
% 0.17/0.45    inference(avatar_split_clause,[],[f526,f409,f362,f539])).
% 0.17/0.45  fof(f362,plain,(
% 0.17/0.45    spl3_42 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.17/0.45  fof(f409,plain,(
% 0.17/0.45    spl3_46 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.17/0.45  fof(f526,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | (~spl3_42 | ~spl3_46)),
% 0.17/0.45    inference(superposition,[],[f363,f410])).
% 0.17/0.45  fof(f410,plain,(
% 0.17/0.45    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_46),
% 0.17/0.45    inference(avatar_component_clause,[],[f409])).
% 0.17/0.45  fof(f363,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_42),
% 0.17/0.45    inference(avatar_component_clause,[],[f362])).
% 0.17/0.45  fof(f515,plain,(
% 0.17/0.45    spl3_45 | spl3_46 | ~spl3_47 | ~spl3_44),
% 0.17/0.45    inference(avatar_split_clause,[],[f469,f395,f412,f409,f406])).
% 0.17/0.45  fof(f406,plain,(
% 0.17/0.45    spl3_45 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.17/0.45  fof(f412,plain,(
% 0.17/0.45    spl3_47 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.17/0.45  fof(f395,plain,(
% 0.17/0.45    spl3_44 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.17/0.45  fof(f469,plain,(
% 0.17/0.45    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_44),
% 0.17/0.45    inference(resolution,[],[f396,f72])).
% 0.17/0.45  fof(f72,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.17/0.45    inference(cnf_transformation,[],[f47])).
% 0.17/0.45  fof(f47,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(nnf_transformation,[],[f35])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(flattening,[],[f34])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f10])).
% 0.17/0.45  fof(f10,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.45  fof(f396,plain,(
% 0.17/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_44),
% 0.17/0.45    inference(avatar_component_clause,[],[f395])).
% 0.17/0.45  fof(f496,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.17/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.17/0.45  fof(f492,plain,(
% 0.17/0.45    spl3_56 | ~spl3_40 | ~spl3_37 | ~spl3_42 | ~spl3_55),
% 0.17/0.45    inference(avatar_split_clause,[],[f491,f457,f362,f314,f342,f487])).
% 0.17/0.45  fof(f342,plain,(
% 0.17/0.45    spl3_40 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.17/0.45  fof(f314,plain,(
% 0.17/0.45    spl3_37 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.17/0.45  fof(f457,plain,(
% 0.17/0.45    spl3_55 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.17/0.45  fof(f491,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_37 | ~spl3_42 | ~spl3_55)),
% 0.17/0.45    inference(trivial_inequality_removal,[],[f490])).
% 0.17/0.45  fof(f490,plain,(
% 0.17/0.45    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_37 | ~spl3_42 | ~spl3_55)),
% 0.17/0.45    inference(forward_demodulation,[],[f480,f315])).
% 0.17/0.45  fof(f315,plain,(
% 0.17/0.45    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_37),
% 0.17/0.45    inference(avatar_component_clause,[],[f314])).
% 0.17/0.45  fof(f480,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_42 | ~spl3_55)),
% 0.17/0.45    inference(resolution,[],[f458,f363])).
% 0.17/0.45  fof(f458,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_55),
% 0.17/0.45    inference(avatar_component_clause,[],[f457])).
% 0.17/0.45  fof(f465,plain,(
% 0.17/0.45    ~spl3_7 | ~spl3_40 | ~spl3_42 | ~spl3_3 | ~spl3_37 | spl3_47),
% 0.17/0.45    inference(avatar_split_clause,[],[f463,f412,f314,f101,f362,f342,f117])).
% 0.17/0.45  fof(f463,plain,(
% 0.17/0.45    ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_37 | spl3_47)),
% 0.17/0.45    inference(trivial_inequality_removal,[],[f462])).
% 0.17/0.45  fof(f462,plain,(
% 0.17/0.45    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_37 | spl3_47)),
% 0.17/0.45    inference(forward_demodulation,[],[f460,f315])).
% 0.17/0.45  fof(f460,plain,(
% 0.17/0.45    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | spl3_47),
% 0.17/0.45    inference(resolution,[],[f413,f79])).
% 0.17/0.45  fof(f79,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f37])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.17/0.45    inference(flattening,[],[f36])).
% 0.17/0.45  fof(f36,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.17/0.45    inference(ennf_transformation,[],[f13])).
% 0.17/0.45  fof(f13,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.17/0.45  fof(f413,plain,(
% 0.17/0.45    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl3_47),
% 0.17/0.45    inference(avatar_component_clause,[],[f412])).
% 0.17/0.45  fof(f459,plain,(
% 0.17/0.45    ~spl3_7 | spl3_55 | ~spl3_3),
% 0.17/0.45    inference(avatar_split_clause,[],[f455,f101,f457,f117])).
% 0.17/0.45  fof(f455,plain,(
% 0.17/0.45    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.17/0.45    inference(resolution,[],[f81,f102])).
% 0.17/0.45  fof(f102,plain,(
% 0.17/0.45    v2_funct_1(sK2) | ~spl3_3),
% 0.17/0.45    inference(avatar_component_clause,[],[f101])).
% 0.17/0.45  % (28533)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.17/0.45  fof(f81,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f39])).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.17/0.45    inference(flattening,[],[f38])).
% 0.17/0.45  fof(f38,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.17/0.45    inference(ennf_transformation,[],[f16])).
% 0.17/0.45  fof(f16,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.17/0.45  fof(f425,plain,(
% 0.17/0.45    spl3_50 | ~spl3_44),
% 0.17/0.45    inference(avatar_split_clause,[],[f404,f395,f423])).
% 0.17/0.45  fof(f404,plain,(
% 0.17/0.45    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_44),
% 0.17/0.45    inference(resolution,[],[f396,f70])).
% 0.17/0.45  fof(f70,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f32])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f9])).
% 0.17/0.45  fof(f9,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.17/0.45  fof(f401,plain,(
% 0.17/0.45    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.17/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.17/0.45  fof(f400,plain,(
% 0.17/0.45    spl3_44 | ~spl3_40 | ~spl3_37 | ~spl3_42 | ~spl3_43),
% 0.17/0.45    inference(avatar_split_clause,[],[f399,f384,f362,f314,f342,f395])).
% 0.17/0.45  fof(f384,plain,(
% 0.17/0.45    spl3_43 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.17/0.45  fof(f399,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_37 | ~spl3_42 | ~spl3_43)),
% 0.17/0.45    inference(trivial_inequality_removal,[],[f398])).
% 0.17/0.45  fof(f398,plain,(
% 0.17/0.45    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_37 | ~spl3_42 | ~spl3_43)),
% 0.17/0.45    inference(forward_demodulation,[],[f388,f315])).
% 0.17/0.45  fof(f388,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_42 | ~spl3_43)),
% 0.17/0.45    inference(resolution,[],[f385,f363])).
% 0.17/0.45  fof(f385,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_43),
% 0.17/0.45    inference(avatar_component_clause,[],[f384])).
% 0.17/0.45  fof(f386,plain,(
% 0.17/0.45    ~spl3_7 | spl3_43 | ~spl3_3),
% 0.17/0.45    inference(avatar_split_clause,[],[f381,f101,f384,f117])).
% 0.17/0.45  fof(f381,plain,(
% 0.17/0.45    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.17/0.45    inference(resolution,[],[f80,f102])).
% 0.17/0.45  fof(f80,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f37])).
% 0.17/0.45  fof(f364,plain,(
% 0.17/0.45    spl3_42 | ~spl3_27 | ~spl3_35),
% 0.17/0.45    inference(avatar_split_clause,[],[f352,f302,f235,f362])).
% 0.17/0.45  fof(f235,plain,(
% 0.17/0.45    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.17/0.45  fof(f352,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_27 | ~spl3_35)),
% 0.17/0.45    inference(superposition,[],[f236,f303])).
% 0.17/0.45  fof(f236,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_27),
% 0.17/0.45    inference(avatar_component_clause,[],[f235])).
% 0.17/0.45  fof(f347,plain,(
% 0.17/0.45    spl3_40 | ~spl3_28 | ~spl3_35),
% 0.17/0.45    inference(avatar_split_clause,[],[f333,f302,f239,f342])).
% 0.17/0.45  fof(f239,plain,(
% 0.17/0.45    spl3_28 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.17/0.45  fof(f333,plain,(
% 0.17/0.45    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_28 | ~spl3_35)),
% 0.17/0.45    inference(superposition,[],[f240,f303])).
% 0.17/0.45  fof(f240,plain,(
% 0.17/0.45    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_28),
% 0.17/0.45    inference(avatar_component_clause,[],[f239])).
% 0.17/0.45  fof(f311,plain,(
% 0.17/0.45    k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 != k2_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 0.17/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.17/0.45  fof(f310,plain,(
% 0.17/0.45    ~spl3_27 | spl3_36),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f309])).
% 0.17/0.45  fof(f309,plain,(
% 0.17/0.45    $false | (~spl3_27 | spl3_36)),
% 0.17/0.45    inference(subsumption_resolution,[],[f236,f308])).
% 0.17/0.45  fof(f308,plain,(
% 0.17/0.45    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl3_36),
% 0.17/0.45    inference(resolution,[],[f306,f71])).
% 0.17/0.45  fof(f71,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f33])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f19])).
% 0.17/0.45  fof(f19,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.17/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.17/0.45  fof(f306,plain,(
% 0.17/0.45    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_36),
% 0.17/0.45    inference(avatar_component_clause,[],[f305])).
% 0.17/0.45  fof(f305,plain,(
% 0.17/0.45    spl3_36 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.17/0.45  fof(f307,plain,(
% 0.17/0.45    ~spl3_28 | spl3_34 | spl3_35 | ~spl3_36 | ~spl3_27 | ~spl3_33),
% 0.17/0.45    inference(avatar_split_clause,[],[f296,f278,f235,f305,f302,f299,f239])).
% 0.17/0.45  fof(f299,plain,(
% 0.17/0.45    spl3_34 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.17/0.45  fof(f278,plain,(
% 0.17/0.45    spl3_33 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.17/0.45  fof(f296,plain,(
% 0.17/0.45    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_27 | ~spl3_33)),
% 0.17/0.45    inference(resolution,[],[f279,f236])).
% 0.17/0.45  fof(f279,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1)) ) | ~spl3_33),
% 0.17/0.45    inference(avatar_component_clause,[],[f278])).
% 0.17/0.45  fof(f293,plain,(
% 0.17/0.45    spl3_27 | ~spl3_19 | ~spl3_23),
% 0.17/0.45    inference(avatar_split_clause,[],[f292,f212,f177,f235])).
% 0.17/0.45  fof(f177,plain,(
% 0.17/0.45    spl3_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.17/0.45  fof(f292,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_19 | ~spl3_23)),
% 0.17/0.45    inference(forward_demodulation,[],[f178,f213])).
% 0.17/0.45  fof(f178,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_19),
% 0.17/0.45    inference(avatar_component_clause,[],[f177])).
% 0.17/0.45  fof(f285,plain,(
% 0.17/0.45    ~spl3_5 | spl3_32),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f282])).
% 0.17/0.45  fof(f282,plain,(
% 0.17/0.45    $false | (~spl3_5 | spl3_32)),
% 0.17/0.45    inference(subsumption_resolution,[],[f110,f281])).
% 0.17/0.45  fof(f281,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_32),
% 0.17/0.45    inference(resolution,[],[f276,f69])).
% 0.17/0.45  fof(f69,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.17/0.45  fof(f276,plain,(
% 0.17/0.45    ~v1_relat_1(sK2) | spl3_32),
% 0.17/0.45    inference(avatar_component_clause,[],[f275])).
% 0.17/0.45  fof(f110,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.17/0.45    inference(avatar_component_clause,[],[f109])).
% 0.17/0.46  fof(f109,plain,(
% 0.17/0.46    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.46  fof(f280,plain,(
% 0.17/0.46    ~spl3_32 | spl3_33 | ~spl3_7),
% 0.17/0.46    inference(avatar_split_clause,[],[f273,f117,f278,f275])).
% 0.17/0.46  fof(f273,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.17/0.46    inference(resolution,[],[f272,f67])).
% 0.17/0.46  fof(f67,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f46])).
% 0.17/0.46  fof(f46,plain,(
% 0.17/0.46    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.17/0.46    inference(nnf_transformation,[],[f30])).
% 0.17/0.46  fof(f30,plain,(
% 0.17/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.17/0.46    inference(flattening,[],[f29])).
% 0.17/0.46  fof(f29,plain,(
% 0.17/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.17/0.46    inference(ennf_transformation,[],[f11])).
% 0.17/0.46  fof(f11,axiom,(
% 0.17/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.17/0.46  fof(f272,plain,(
% 0.17/0.46    ( ! [X0,X1] : (v1_partfun1(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.17/0.46    inference(resolution,[],[f91,f118])).
% 0.17/0.46  fof(f118,plain,(
% 0.17/0.46    v1_funct_1(sK2) | ~spl3_7),
% 0.17/0.46    inference(avatar_component_clause,[],[f117])).
% 0.17/0.46  fof(f91,plain,(
% 0.17/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.17/0.46    inference(duplicate_literal_removal,[],[f82])).
% 0.17/0.46  fof(f82,plain,(
% 0.17/0.46    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f41])).
% 0.17/0.46  fof(f41,plain,(
% 0.17/0.46    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.17/0.46    inference(flattening,[],[f40])).
% 0.17/0.46  fof(f40,plain,(
% 0.17/0.46    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.17/0.46    inference(ennf_transformation,[],[f12])).
% 0.17/0.46  fof(f12,axiom,(
% 0.17/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.17/0.46  fof(f241,plain,(
% 0.17/0.46    spl3_28 | ~spl3_20 | ~spl3_23),
% 0.17/0.46    inference(avatar_split_clause,[],[f227,f212,f182,f239])).
% 0.17/0.46  fof(f182,plain,(
% 0.17/0.46    spl3_20 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.17/0.46  fof(f227,plain,(
% 0.17/0.46    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_20 | ~spl3_23)),
% 0.17/0.46    inference(superposition,[],[f183,f213])).
% 0.17/0.46  fof(f183,plain,(
% 0.17/0.46    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_20),
% 0.17/0.46    inference(avatar_component_clause,[],[f182])).
% 0.17/0.46  fof(f223,plain,(
% 0.17/0.46    spl3_23 | ~spl3_17 | ~spl3_22),
% 0.17/0.46    inference(avatar_split_clause,[],[f221,f207,f162,f212])).
% 0.17/0.46  fof(f162,plain,(
% 0.17/0.46    spl3_17 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.17/0.46  fof(f207,plain,(
% 0.17/0.46    spl3_22 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.17/0.46  fof(f221,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_17 | ~spl3_22)),
% 0.17/0.46    inference(superposition,[],[f163,f208])).
% 0.17/0.46  fof(f208,plain,(
% 0.17/0.46    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_22),
% 0.17/0.46    inference(avatar_component_clause,[],[f207])).
% 0.17/0.46  fof(f163,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_17),
% 0.17/0.46    inference(avatar_component_clause,[],[f162])).
% 0.17/0.46  fof(f209,plain,(
% 0.17/0.46    spl3_22 | ~spl3_5 | ~spl3_15 | ~spl3_16),
% 0.17/0.46    inference(avatar_split_clause,[],[f205,f158,f154,f109,f207])).
% 0.17/0.46  fof(f205,plain,(
% 0.17/0.46    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_5 | ~spl3_15 | ~spl3_16)),
% 0.17/0.46    inference(forward_demodulation,[],[f204,f159])).
% 0.17/0.46  fof(f204,plain,(
% 0.17/0.46    k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_5 | ~spl3_15)),
% 0.17/0.46    inference(forward_demodulation,[],[f202,f155])).
% 0.17/0.46  fof(f202,plain,(
% 0.17/0.46    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_5),
% 0.17/0.46    inference(resolution,[],[f70,f110])).
% 0.17/0.46  fof(f199,plain,(
% 0.17/0.46    ~spl3_8 | ~spl3_21 | spl3_9 | ~spl3_15),
% 0.17/0.46    inference(avatar_split_clause,[],[f194,f154,f125,f197,f121])).
% 0.17/0.46  fof(f121,plain,(
% 0.17/0.46    spl3_8 <=> l1_struct_0(sK1)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.17/0.46  fof(f197,plain,(
% 0.17/0.46    spl3_21 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.17/0.46  fof(f125,plain,(
% 0.17/0.46    spl3_9 <=> v2_struct_0(sK1)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.17/0.46  fof(f194,plain,(
% 0.17/0.46    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | (spl3_9 | ~spl3_15)),
% 0.17/0.46    inference(forward_demodulation,[],[f193,f155])).
% 0.17/0.46  fof(f193,plain,(
% 0.17/0.46    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | spl3_9),
% 0.17/0.46    inference(resolution,[],[f63,f126])).
% 0.17/0.46  fof(f126,plain,(
% 0.17/0.46    ~v2_struct_0(sK1) | spl3_9),
% 0.17/0.46    inference(avatar_component_clause,[],[f125])).
% 0.17/0.46  fof(f63,plain,(
% 0.17/0.46    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.17/0.46    inference(cnf_transformation,[],[f25])).
% 0.17/0.46  fof(f25,plain,(
% 0.17/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.17/0.46    inference(flattening,[],[f24])).
% 0.17/0.46  fof(f24,plain,(
% 0.17/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.17/0.46    inference(ennf_transformation,[],[f15])).
% 0.17/0.46  fof(f15,axiom,(
% 0.17/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.17/0.46  fof(f184,plain,(
% 0.17/0.46    spl3_20 | ~spl3_6 | ~spl3_15 | ~spl3_16),
% 0.17/0.46    inference(avatar_split_clause,[],[f180,f158,f154,f113,f182])).
% 0.17/0.46  fof(f113,plain,(
% 0.17/0.46    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.17/0.46  fof(f180,plain,(
% 0.17/0.46    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_15 | ~spl3_16)),
% 0.17/0.46    inference(forward_demodulation,[],[f167,f159])).
% 0.17/0.46  fof(f167,plain,(
% 0.17/0.46    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_15)),
% 0.17/0.46    inference(superposition,[],[f114,f155])).
% 0.17/0.46  fof(f114,plain,(
% 0.17/0.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.17/0.46    inference(avatar_component_clause,[],[f113])).
% 0.17/0.46  fof(f179,plain,(
% 0.17/0.46    spl3_19 | ~spl3_5 | ~spl3_15 | ~spl3_16),
% 0.17/0.46    inference(avatar_split_clause,[],[f175,f158,f154,f109,f177])).
% 0.17/0.46  fof(f175,plain,(
% 0.17/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_15 | ~spl3_16)),
% 0.17/0.46    inference(forward_demodulation,[],[f166,f159])).
% 0.17/0.46  fof(f166,plain,(
% 0.17/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_15)),
% 0.17/0.46    inference(superposition,[],[f110,f155])).
% 0.17/0.46  fof(f174,plain,(
% 0.17/0.46    spl3_17 | ~spl3_4 | ~spl3_15 | ~spl3_16),
% 0.17/0.46    inference(avatar_split_clause,[],[f173,f158,f154,f105,f162])).
% 0.17/0.46  fof(f105,plain,(
% 0.17/0.46    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.46  fof(f173,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_15 | ~spl3_16)),
% 0.17/0.46    inference(forward_demodulation,[],[f165,f159])).
% 0.17/0.46  fof(f165,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_15)),
% 0.17/0.46    inference(superposition,[],[f106,f155])).
% 0.17/0.46  fof(f106,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.17/0.46    inference(avatar_component_clause,[],[f105])).
% 0.17/0.46  fof(f160,plain,(
% 0.17/0.46    spl3_16 | ~spl3_10),
% 0.17/0.46    inference(avatar_split_clause,[],[f152,f129,f158])).
% 0.17/0.46  fof(f129,plain,(
% 0.17/0.46    spl3_10 <=> l1_struct_0(sK0)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.17/0.46  fof(f152,plain,(
% 0.17/0.46    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.17/0.46    inference(resolution,[],[f61,f130])).
% 0.17/0.46  fof(f130,plain,(
% 0.17/0.46    l1_struct_0(sK0) | ~spl3_10),
% 0.17/0.46    inference(avatar_component_clause,[],[f129])).
% 0.17/0.46  fof(f61,plain,(
% 0.17/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f22])).
% 0.17/0.46  fof(f22,plain,(
% 0.17/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.17/0.46    inference(ennf_transformation,[],[f14])).
% 0.17/0.46  fof(f14,axiom,(
% 0.17/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.17/0.46  fof(f156,plain,(
% 0.17/0.46    spl3_15 | ~spl3_8),
% 0.17/0.46    inference(avatar_split_clause,[],[f151,f121,f154])).
% 0.17/0.46  fof(f151,plain,(
% 0.17/0.46    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.17/0.46    inference(resolution,[],[f61,f122])).
% 0.17/0.46  fof(f122,plain,(
% 0.17/0.46    l1_struct_0(sK1) | ~spl3_8),
% 0.17/0.46    inference(avatar_component_clause,[],[f121])).
% 0.17/0.46  fof(f146,plain,(
% 0.17/0.46    spl3_13 | ~spl3_12),
% 0.17/0.46    inference(avatar_split_clause,[],[f141,f137,f144])).
% 0.17/0.46  fof(f144,plain,(
% 0.17/0.46    spl3_13 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.17/0.46  fof(f137,plain,(
% 0.17/0.46    spl3_12 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.17/0.46  % (28540)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.17/0.46  fof(f141,plain,(
% 0.17/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_12),
% 0.17/0.46    inference(superposition,[],[f60,f138])).
% 0.17/0.46  fof(f138,plain,(
% 0.17/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_12),
% 0.17/0.46    inference(avatar_component_clause,[],[f137])).
% 0.17/0.46  fof(f60,plain,(
% 0.17/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.17/0.46    inference(cnf_transformation,[],[f3])).
% 0.17/0.46  fof(f3,axiom,(
% 0.17/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.17/0.46  fof(f139,plain,(
% 0.17/0.46    spl3_12),
% 0.17/0.46    inference(avatar_split_clause,[],[f58,f137])).
% 0.17/0.46  fof(f58,plain,(
% 0.17/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.17/0.46    inference(cnf_transformation,[],[f4])).
% 0.17/0.46  fof(f4,axiom,(
% 0.17/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.17/0.46  fof(f135,plain,(
% 0.17/0.46    spl3_11),
% 0.17/0.46    inference(avatar_split_clause,[],[f57,f133])).
% 0.17/0.46  fof(f57,plain,(
% 0.17/0.46    v1_xboole_0(k1_xboole_0)),
% 0.17/0.46    inference(cnf_transformation,[],[f1])).
% 0.17/0.46  fof(f1,axiom,(
% 0.17/0.46    v1_xboole_0(k1_xboole_0)),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.17/0.46  fof(f131,plain,(
% 0.17/0.46    spl3_10),
% 0.17/0.46    inference(avatar_split_clause,[],[f48,f129])).
% 0.17/0.46  fof(f48,plain,(
% 0.17/0.46    l1_struct_0(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f45,plain,(
% 0.17/0.46    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.17/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43,f42])).
% 0.17/0.46  fof(f42,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.17/0.46    introduced(choice_axiom,[])).
% 0.17/0.46  fof(f43,plain,(
% 0.17/0.46    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.17/0.46    introduced(choice_axiom,[])).
% 0.17/0.46  fof(f44,plain,(
% 0.17/0.46    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.17/0.46    introduced(choice_axiom,[])).
% 0.17/0.46  fof(f21,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.17/0.46    inference(flattening,[],[f20])).
% 0.17/0.46  fof(f20,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.17/0.46    inference(ennf_transformation,[],[f18])).
% 0.17/0.46  fof(f18,negated_conjecture,(
% 0.17/0.46    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.17/0.46    inference(negated_conjecture,[],[f17])).
% 0.17/0.46  fof(f17,conjecture,(
% 0.17/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.17/0.46  fof(f127,plain,(
% 0.17/0.46    ~spl3_9),
% 0.17/0.46    inference(avatar_split_clause,[],[f49,f125])).
% 0.17/0.46  fof(f49,plain,(
% 0.17/0.46    ~v2_struct_0(sK1)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f123,plain,(
% 0.17/0.46    spl3_8),
% 0.17/0.46    inference(avatar_split_clause,[],[f50,f121])).
% 0.17/0.46  fof(f50,plain,(
% 0.17/0.46    l1_struct_0(sK1)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f119,plain,(
% 0.17/0.46    spl3_7),
% 0.17/0.46    inference(avatar_split_clause,[],[f51,f117])).
% 0.17/0.46  fof(f51,plain,(
% 0.17/0.46    v1_funct_1(sK2)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f115,plain,(
% 0.17/0.46    spl3_6),
% 0.17/0.46    inference(avatar_split_clause,[],[f52,f113])).
% 0.17/0.46  fof(f52,plain,(
% 0.17/0.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f111,plain,(
% 0.17/0.46    spl3_5),
% 0.17/0.46    inference(avatar_split_clause,[],[f53,f109])).
% 0.17/0.46  fof(f53,plain,(
% 0.17/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f107,plain,(
% 0.17/0.46    spl3_4),
% 0.17/0.46    inference(avatar_split_clause,[],[f54,f105])).
% 0.17/0.46  fof(f54,plain,(
% 0.17/0.46    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f103,plain,(
% 0.17/0.46    spl3_3),
% 0.17/0.46    inference(avatar_split_clause,[],[f55,f101])).
% 0.17/0.46  fof(f55,plain,(
% 0.17/0.46    v2_funct_1(sK2)),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  fof(f99,plain,(
% 0.17/0.46    ~spl3_1 | ~spl3_2),
% 0.17/0.46    inference(avatar_split_clause,[],[f56,f97,f94])).
% 0.17/0.46  fof(f94,plain,(
% 0.17/0.46    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.46  fof(f56,plain,(
% 0.17/0.46    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.17/0.46    inference(cnf_transformation,[],[f45])).
% 0.17/0.46  % SZS output end Proof for theBenchmark
% 0.17/0.46  % (28537)------------------------------
% 0.17/0.46  % (28537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.46  % (28537)Termination reason: Refutation
% 0.17/0.46  
% 0.17/0.46  % (28537)Memory used [KB]: 11129
% 0.17/0.46  % (28537)Time elapsed: 0.077 s
% 0.17/0.46  % (28537)------------------------------
% 0.17/0.46  % (28537)------------------------------
% 0.17/0.46  % (28530)Success in time 0.137 s
%------------------------------------------------------------------------------
