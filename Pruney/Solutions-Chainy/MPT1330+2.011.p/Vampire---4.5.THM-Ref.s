%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 270 expanded)
%              Number of leaves         :   36 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 (1078 expanded)
%              Number of equality atoms :  108 ( 359 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f68,f72,f76,f80,f84,f88,f94,f98,f106,f116,f133,f140,f152,f162,f171,f189,f202,f206,f209,f243])).

fof(f243,plain,
    ( spl3_19
    | ~ spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f240,f109,f198,f169])).

fof(f169,plain,
    ( spl3_19
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f198,plain,
    ( spl3_24
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f109,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f240,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f239,f110])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl3_12 ),
    inference(resolution,[],[f238,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f238,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f124,f110])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v4_relat_1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1) ) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f209,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f206,plain,
    ( spl3_2
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f204,f195,f63])).

fof(f63,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f195,plain,
    ( spl3_23
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f204,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_23 ),
    inference(resolution,[],[f196,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f196,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f202,plain,
    ( spl3_23
    | spl3_24
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f190,f109,f114,f78,f198,f195])).

fof(f78,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f190,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_12 ),
    inference(resolution,[],[f110,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f189,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f188,f96,f92,f70,f109])).

fof(f70,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f96,plain,
    ( spl3_10
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f187,f97])).

fof(f97,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f187,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f71,f93])).

fof(f93,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f171,plain,
    ( ~ spl3_19
    | spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f166,f159,f131,f169])).

fof(f131,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f159,plain,
    ( spl3_17
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f166,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f132,f160])).

fof(f160,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f132,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f162,plain,
    ( ~ spl3_12
    | spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f156,f150,f159,f109])).

fof(f150,plain,
    ( spl3_16
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f156,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f151])).

fof(f151,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f148,f96,f92,f70,f150])).

fof(f148,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f147,f128])).

fof(f128,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f127,f97])).

fof(f127,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f125,f93])).

fof(f125,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_4 ),
    inference(resolution,[],[f56,f71])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f147,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f146,f97])).

fof(f146,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f144,f93])).

fof(f144,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f55,f71])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f140,plain,
    ( spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f135,f70,f138])).

fof(f138,plain,
    ( spl3_15
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f135,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(resolution,[],[f134,f71])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f123,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
      | k1_xboole_0 = k10_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f133,plain,
    ( ~ spl3_14
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f129,f104,f96,f92,f70,f131])).

fof(f104,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | spl3_11 ),
    inference(superposition,[],[f105,f128])).

fof(f105,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f116,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f112,f96,f92,f74,f114])).

fof(f74,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f75,f93])).

fof(f75,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f106,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f102,f96,f92,f59,f104])).

fof(f59,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f99,f97])).

fof(f99,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f60,f93])).

fof(f60,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f98,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f90,f86,f96])).

fof(f86,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f44,f87])).

fof(f87,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f44,plain,(
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

fof(f94,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f89,f82,f92])).

fof(f82,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f89,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f44,f83])).

fof(f83,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f88,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f86])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f84,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f40,f66,f63])).

fof(f66,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f59])).

fof(f41,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (21139)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.42  % (21139)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.43  % (21148)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f244,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f61,f68,f72,f76,f80,f84,f88,f94,f98,f106,f116,f133,f140,f152,f162,f171,f189,f202,f206,f209,f243])).
% 0.21/0.43  fof(f243,plain,(
% 0.21/0.43    spl3_19 | ~spl3_24 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f240,f109,f198,f169])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    spl3_19 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    spl3_24 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f240,plain,(
% 0.21/0.43    ~v1_partfun1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_12),
% 0.21/0.43    inference(resolution,[],[f239,f110])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f109])).
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0) ) | ~spl3_12),
% 0.21/0.43    inference(resolution,[],[f238,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.43  fof(f238,plain,(
% 0.21/0.43    ( ! [X0] : (~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0)) ) | ~spl3_12),
% 0.21/0.43    inference(resolution,[],[f124,f110])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1)) )),
% 0.21/0.43    inference(resolution,[],[f49,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.43  fof(f209,plain,(
% 0.21/0.43    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f206,plain,(
% 0.21/0.43    spl3_2 | ~spl3_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f204,f195,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f195,plain,(
% 0.21/0.43    spl3_23 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.43  fof(f204,plain,(
% 0.21/0.43    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_23),
% 0.21/0.43    inference(resolution,[],[f196,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f195])).
% 0.21/0.43  fof(f202,plain,(
% 0.21/0.43    spl3_23 | spl3_24 | ~spl3_6 | ~spl3_13 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f190,f109,f114,f78,f198,f195])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1)) | ~spl3_12),
% 0.21/0.43    inference(resolution,[],[f110,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    spl3_12 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f188,f96,f92,f70,f109])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl3_10 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f187,f97])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f96])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9)),
% 0.21/0.43    inference(forward_demodulation,[],[f71,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f70])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    ~spl3_19 | spl3_14 | ~spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f166,f159,f131,f169])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl3_14 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    spl3_17 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k1_relat_1(sK2) | (spl3_14 | ~spl3_17)),
% 0.21/0.43    inference(superposition,[],[f132,f160])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | ~spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f159])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl3_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f131])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    ~spl3_12 | spl3_17 | ~spl3_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f156,f150,f159,f109])).
% 0.21/0.43  fof(f150,plain,(
% 0.21/0.43    spl3_16 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.21/0.43    inference(superposition,[],[f52,f151])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f150])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    spl3_16 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f148,f96,f92,f70,f150])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f147,f128])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f127,f97])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.43    inference(forward_demodulation,[],[f125,f93])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_4),
% 0.21/0.43    inference(resolution,[],[f56,f71])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f146,f97])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_9)),
% 0.21/0.43    inference(forward_demodulation,[],[f144,f93])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) | ~spl3_4),
% 0.21/0.43    inference(resolution,[],[f55,f71])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl3_15 | ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f135,f70,f138])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    spl3_15 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_4),
% 0.21/0.43    inference(resolution,[],[f134,f71])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(resolution,[],[f123,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(k2_relat_1(X0),X1) | k1_xboole_0 = k10_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.43    inference(resolution,[],[f48,f51])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ~spl3_14 | ~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f129,f104,f96,f92,f70,f131])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    spl3_11 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_4 | ~spl3_9 | ~spl3_10 | spl3_11)),
% 0.21/0.43    inference(superposition,[],[f105,f128])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f104])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    spl3_13 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f112,f96,f92,f74,f114])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f101,f97])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9)),
% 0.21/0.43    inference(superposition,[],[f75,f93])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f74])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ~spl3_11 | spl3_1 | ~spl3_9 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f102,f96,f92,f59,f104])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f99,f97])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9)),
% 0.21/0.43    inference(superposition,[],[f60,f93])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f59])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl3_10 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f90,f86,f96])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.21/0.43    inference(resolution,[],[f44,f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f86])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl3_9 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f89,f82,f92])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl3_7 <=> l1_struct_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.21/0.43    inference(resolution,[],[f44,f83])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f86])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    l1_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f12])).
% 0.21/0.43  fof(f12,conjecture,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f82])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    l1_struct_0(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f78])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    v1_funct_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f74])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f39,f70])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ~spl3_2 | spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f40,f66,f63])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f41,f59])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (21139)------------------------------
% 0.21/0.43  % (21139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (21139)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (21139)Memory used [KB]: 10746
% 0.21/0.43  % (21139)Time elapsed: 0.042 s
% 0.21/0.43  % (21139)------------------------------
% 0.21/0.43  % (21139)------------------------------
% 0.21/0.43  % (21129)Success in time 0.076 s
%------------------------------------------------------------------------------
