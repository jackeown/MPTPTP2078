%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 297 expanded)
%              Number of leaves         :   36 ( 141 expanded)
%              Depth                    :    9
%              Number of atoms          :  444 (1162 expanded)
%              Number of equality atoms :   87 ( 332 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f61,f66,f71,f76,f81,f86,f99,f128,f134,f140,f165,f166,f167,f175,f183,f201,f222,f229,f261,f280,f285,f315,f351,f357,f364])).

fof(f364,plain,
    ( ~ spl3_6
    | spl3_36
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl3_6
    | spl3_36
    | ~ spl3_42
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f362,f356])).

fof(f356,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl3_43
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f362,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_6
    | spl3_36
    | ~ spl3_42 ),
    inference(unit_resulting_resolution,[],[f75,f314,f350,f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f350,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl3_42
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f314,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl3_36
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f357,plain,
    ( spl3_43
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f352,f277,f54,f354])).

fof(f54,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f277,plain,
    ( spl3_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f279,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f277])).

fof(f351,plain,
    ( spl3_42
    | ~ spl3_2
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f346,f282,f54,f348])).

fof(f282,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f346,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f284,f55])).

fof(f284,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f282])).

fof(f315,plain,
    ( ~ spl3_36
    | ~ spl3_3
    | spl3_27 ),
    inference(avatar_split_clause,[],[f270,f226,f58,f312])).

fof(f58,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f226,plain,
    ( spl3_27
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f270,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_3
    | spl3_27 ),
    inference(backward_demodulation,[],[f228,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f228,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f226])).

fof(f285,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f264,f158,f58,f282])).

fof(f158,plain,
    ( spl3_19
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f264,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f160,f60])).

fof(f160,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f280,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f263,f153,f58,f277])).

fof(f153,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f263,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f155,f60])).

fof(f155,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f261,plain,
    ( spl3_2
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_19
    | spl3_27 ),
    inference(avatar_split_clause,[],[f237,f226,f158,f153,f73,f54])).

fof(f237,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_19
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f75,f228,f160,f155,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f229,plain,
    ( ~ spl3_27
    | ~ spl3_20
    | ~ spl3_21
    | spl3_26 ),
    inference(avatar_split_clause,[],[f224,f219,f179,f171,f226])).

fof(f171,plain,
    ( spl3_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f179,plain,
    ( spl3_21
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f219,plain,
    ( spl3_26
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f224,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_20
    | ~ spl3_21
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f173,f181,f221,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f221,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f219])).

fof(f181,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f173,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f222,plain,
    ( ~ spl3_26
    | spl3_17
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f217,f198,f153,f148,f219])).

fof(f148,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f198,plain,
    ( spl3_23
  <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f217,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_17
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f216,f200])).

fof(f200,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f198])).

fof(f216,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f209,f155])).

fof(f209,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_17 ),
    inference(superposition,[],[f150,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f150,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f201,plain,
    ( spl3_23
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f196,f153,f198])).

fof(f196,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f155,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( spl3_21
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f177,f153,f179])).

fof(f177,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_18 ),
    inference(resolution,[],[f38,f155])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f175,plain,
    ( spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f169,f153,f171])).

fof(f169,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f155,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f167,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f137,f96,f158])).

fof(f96,plain,
    ( spl3_9
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f137,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f139,f98])).

fof(f98,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f139,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f166,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f163,f131,f96,f153])).

fof(f131,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f133,f98])).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f165,plain,
    ( ~ spl3_17
    | ~ spl3_9
    | spl3_14 ),
    inference(avatar_split_clause,[],[f162,f125,f96,f148])).

fof(f125,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f162,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_9
    | spl3_14 ),
    inference(backward_demodulation,[],[f127,f98])).

fof(f127,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f140,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f135,f78,f68,f137])).

fof(f68,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f135,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f94,f80])).

fof(f80,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f94,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f70,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f70,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f134,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f129,f78,f63,f131])).

fof(f63,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f93,f80])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f65,f33])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f128,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f123,f78,f49,f125])).

fof(f49,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f92,f80])).

fof(f92,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | spl3_1 ),
    inference(superposition,[],[f51,f33])).

fof(f51,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f99,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f88,f83,f96])).

fof(f83,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f85,f33])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f83])).

fof(f26,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f23,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f23,plain,
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f81,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f78])).

fof(f27,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f31,f58,f54])).

fof(f31,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:59:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (4263)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (4263)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f365,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f52,f61,f66,f71,f76,f81,f86,f99,f128,f134,f140,f165,f166,f167,f175,f183,f201,f222,f229,f261,f280,f285,f315,f351,f357,f364])).
% 0.21/0.47  fof(f364,plain,(
% 0.21/0.47    ~spl3_6 | spl3_36 | ~spl3_42 | ~spl3_43),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f363])).
% 0.21/0.47  fof(f363,plain,(
% 0.21/0.47    $false | (~spl3_6 | spl3_36 | ~spl3_42 | ~spl3_43)),
% 0.21/0.47    inference(subsumption_resolution,[],[f362,f356])).
% 0.21/0.47  fof(f356,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_43),
% 0.21/0.47    inference(avatar_component_clause,[],[f354])).
% 0.21/0.47  fof(f354,plain,(
% 0.21/0.47    spl3_43 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.47  fof(f362,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_6 | spl3_36 | ~spl3_42)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f75,f314,f350,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.47  fof(f350,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_42),
% 0.21/0.47    inference(avatar_component_clause,[],[f348])).
% 0.21/0.47  fof(f348,plain,(
% 0.21/0.47    spl3_42 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    ~v1_partfun1(sK2,k1_xboole_0) | spl3_36),
% 0.21/0.47    inference(avatar_component_clause,[],[f312])).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    spl3_36 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f357,plain,(
% 0.21/0.47    spl3_43 | ~spl3_2 | ~spl3_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f352,f277,f54,f354])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    spl3_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.47  fof(f352,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_2 | ~spl3_29)),
% 0.21/0.47    inference(forward_demodulation,[],[f279,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | ~spl3_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f277])).
% 0.21/0.47  fof(f351,plain,(
% 0.21/0.47    spl3_42 | ~spl3_2 | ~spl3_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f346,f282,f54,f348])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    spl3_30 <=> v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.47  fof(f346,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_30)),
% 0.21/0.47    inference(forward_demodulation,[],[f284,f55])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | ~spl3_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f282])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    ~spl3_36 | ~spl3_3 | spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f270,f226,f58,f312])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    spl3_27 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    ~v1_partfun1(sK2,k1_xboole_0) | (~spl3_3 | spl3_27)),
% 0.21/0.47    inference(backward_demodulation,[],[f228,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f226])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    spl3_30 | ~spl3_3 | ~spl3_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f264,f158,f58,f282])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl3_19 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | (~spl3_3 | ~spl3_19)),
% 0.21/0.47    inference(backward_demodulation,[],[f160,f60])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f158])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    spl3_29 | ~spl3_3 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f263,f153,f58,f277])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_18)),
% 0.21/0.47    inference(backward_demodulation,[],[f155,f60])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    spl3_2 | ~spl3_6 | ~spl3_18 | ~spl3_19 | spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f237,f226,f158,f153,f73,f54])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK1) | (~spl3_6 | ~spl3_18 | ~spl3_19 | spl3_27)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f75,f228,f160,f155,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    ~spl3_27 | ~spl3_20 | ~spl3_21 | spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f224,f219,f179,f171,f226])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    spl3_20 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    spl3_21 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    spl3_26 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ~v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_20 | ~spl3_21 | spl3_26)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f173,f181,f221,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f219])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f179])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f171])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ~spl3_26 | spl3_17 | ~spl3_18 | ~spl3_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f217,f198,f153,f148,f219])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl3_17 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl3_23 <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | (spl3_17 | ~spl3_18 | ~spl3_23)),
% 0.21/0.47    inference(forward_demodulation,[],[f216,f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f198])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (spl3_17 | ~spl3_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f209,f155])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_17),
% 0.21/0.47    inference(superposition,[],[f150,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f148])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    spl3_23 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f196,f153,f198])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_18),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f155,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    spl3_21 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f177,f153,f179])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_18),
% 0.21/0.47    inference(resolution,[],[f38,f155])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl3_20 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f169,f153,f171])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_18),
% 0.21/0.47    inference(resolution,[],[f155,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl3_19 | ~spl3_9 | ~spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f164,f137,f96,f158])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl3_9 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl3_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_9 | ~spl3_16)),
% 0.21/0.48    inference(backward_demodulation,[],[f139,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f137])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl3_18 | ~spl3_9 | ~spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f163,f131,f96,f153])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_9 | ~spl3_15)),
% 0.21/0.48    inference(backward_demodulation,[],[f133,f98])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~spl3_17 | ~spl3_9 | spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f162,f125,f96,f148])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl3_14 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_9 | spl3_14)),
% 0.21/0.48    inference(backward_demodulation,[],[f127,f98])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl3_16 | ~spl3_5 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f135,f78,f68,f137])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_7 <=> l1_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~spl3_5),
% 0.21/0.48    inference(superposition,[],[f70,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_15 | ~spl3_4 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f78,f63,f131])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f80])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.48    inference(superposition,[],[f65,f33])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~spl3_14 | spl3_1 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f78,f49,f125])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f80])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~l1_struct_0(sK1) | spl3_1),
% 0.21/0.48    inference(superposition,[],[f51,f33])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_9 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f88,f83,f96])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f85,f33])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f83])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f23,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f78])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    l1_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f73])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f68])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f63])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~spl3_2 | spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f58,f54])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f49])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4263)------------------------------
% 0.21/0.48  % (4263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4263)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4263)Memory used [KB]: 10874
% 0.21/0.48  % (4263)Time elapsed: 0.019 s
% 0.21/0.48  % (4263)------------------------------
% 0.21/0.48  % (4263)------------------------------
% 0.21/0.48  % (4238)Success in time 0.118 s
%------------------------------------------------------------------------------
