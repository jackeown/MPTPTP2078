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
% DateTime   : Thu Dec  3 13:14:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 353 expanded)
%              Number of leaves         :   50 ( 176 expanded)
%              Depth                    :    8
%              Number of atoms          :  569 (1395 expanded)
%              Number of equality atoms :   92 ( 221 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f113,f114,f127,f132,f137,f142,f148,f154,f156,f162,f168,f175,f180,f192,f198,f212,f223,f228,f233,f247,f272,f281,f282,f283,f284,f327,f341])).

fof(f341,plain,(
    spl3_43 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl3_43 ),
    inference(unit_resulting_resolution,[],[f53,f326])).

fof(f326,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl3_43
  <=> v2_funct_1(k6_relat_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f53,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f327,plain,
    ( ~ spl3_6
    | ~ spl3_19
    | ~ spl3_43
    | ~ spl3_23
    | ~ spl3_32
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f322,f278,f270,f244,f189,f324,f165,f85])).

fof(f85,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f165,plain,
    ( spl3_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f189,plain,
    ( spl3_23
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f244,plain,
    ( spl3_32
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f270,plain,
    ( spl3_37
  <=> ! [X0] :
        ( k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f278,plain,
    ( spl3_38
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f322,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_23
    | ~ spl3_32
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f321,f246])).

fof(f246,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f244])).

fof(f321,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(equality_resolution,[],[f297])).

fof(f297,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f296,f280])).

fof(f280,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f278])).

fof(f296,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)) )
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f295,f191])).

fof(f191,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f295,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)) )
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f271,f280])).

fof(f271,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f270])).

fof(f284,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f283,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f282,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f281,plain,
    ( ~ spl3_6
    | ~ spl3_28
    | spl3_38
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f276,f225,f208,f65,f278,f220,f85])).

fof(f220,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f65,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f208,plain,
    ( spl3_27
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f225,plain,
    ( spl3_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f276,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f274,f210])).

fof(f210,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f208])).

fof(f274,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29 ),
    inference(resolution,[],[f42,f227])).

fof(f227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f225])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f272,plain,
    ( ~ spl3_35
    | ~ spl3_36
    | spl3_37
    | spl3_30 ),
    inference(avatar_split_clause,[],[f260,f230,f270,f266,f262])).

fof(f262,plain,
    ( spl3_35
  <=> v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f266,plain,
    ( spl3_36
  <=> v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f230,plain,
    ( spl3_30
  <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f260,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
        | ~ v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0))
        | ~ v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
        | ~ v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl3_30 ),
    inference(resolution,[],[f46,f232])).

fof(f232,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f230])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f247,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f242,f165,f85,f65,f244])).

fof(f242,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f167,f87,f67,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f233,plain,
    ( ~ spl3_30
    | spl3_18
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f218,f200,f159,f230])).

fof(f159,plain,
    ( spl3_18
  <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f200,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f218,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_18
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f161,f202])).

fof(f202,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f161,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f228,plain,
    ( spl3_29
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f217,f200,f151,f225])).

fof(f151,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f153,f202])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f223,plain,
    ( spl3_28
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f216,f200,f145,f220])).

fof(f145,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f216,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f147,f202])).

fof(f147,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f212,plain,
    ( spl3_25
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f211,f195,f116,f200])).

fof(f116,plain,
    ( spl3_11
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f195,plain,
    ( spl3_24
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f211,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f118,f197])).

fof(f197,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f118,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f198,plain,
    ( spl3_24
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f193,f151,f195])).

fof(f193,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f153,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f192,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f187,f165,f85,f65,f189])).

fof(f187,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f167,f87,f67,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f180,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f169,f165,f85,f177])).

fof(f177,plain,
    ( spl3_21
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f169,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f87,f167,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f175,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f170,f165,f85,f172])).

fof(f172,plain,
    ( spl3_20
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f170,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f87,f167,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f163,f151,f165])).

fof(f163,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f153,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f162,plain,
    ( ~ spl3_18
    | ~ spl3_9
    | spl3_12 ),
    inference(avatar_split_clause,[],[f157,f124,f104,f159])).

fof(f104,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( spl3_12
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f157,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_9
    | spl3_12 ),
    inference(forward_demodulation,[],[f126,f106])).

fof(f106,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f126,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f156,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f155,f129,f104,f116])).

fof(f129,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f155,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f131,f106])).

fof(f131,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f154,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f149,f134,f104,f151])).

fof(f134,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f136,f106])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f148,plain,
    ( spl3_16
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f143,f139,f104,f145])).

fof(f139,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f143,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f141,f106])).

fof(f141,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f142,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f122,f109,f80,f139])).

fof(f80,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f109,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f122,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f82,f111])).

fof(f111,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f82,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f137,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f121,f109,f75,f134])).

fof(f75,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f77,f111])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f132,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f120,f109,f70,f129])).

fof(f70,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f120,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f72,f111])).

fof(f72,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f127,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f119,f109,f60,f124])).

fof(f60,plain,
    ( spl3_1
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f62,f111])).

fof(f62,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f114,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f102,f95,f104])).

fof(f95,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f55,f97])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f113,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f101,f90,f109])).

fof(f90,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f92])).

fof(f92,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f98,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f34,f95])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f40,f65])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f60])).

% (5033)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f41,plain,(
    ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (5032)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (5028)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (5031)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (5029)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (5049)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (5029)Refutation not found, incomplete strategy% (5029)------------------------------
% 0.21/0.50  % (5029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5041)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (5048)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (5049)Refutation not found, incomplete strategy% (5049)------------------------------
% 0.21/0.51  % (5049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5049)Memory used [KB]: 10618
% 0.21/0.51  % (5049)Time elapsed: 0.047 s
% 0.21/0.51  % (5049)------------------------------
% 0.21/0.51  % (5049)------------------------------
% 0.21/0.51  % (5026)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (5032)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f113,f114,f127,f132,f137,f142,f148,f154,f156,f162,f168,f175,f180,f192,f198,f212,f223,f228,f233,f247,f272,f281,f282,f283,f284,f327,f341])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    spl3_43),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f336])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    $false | spl3_43),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f53,f326])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f324])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    spl3_43 <=> v2_funct_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ~spl3_6 | ~spl3_19 | ~spl3_43 | ~spl3_23 | ~spl3_32 | ~spl3_37 | ~spl3_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f322,f278,f270,f244,f189,f324,f165,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl3_19 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl3_23 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    spl3_32 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl3_37 <=> ! [X0] : (k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    spl3_38 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f322,plain,(
% 0.21/0.51    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | (~spl3_23 | ~spl3_32 | ~spl3_37 | ~spl3_38)),
% 0.21/0.51    inference(forward_demodulation,[],[f321,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f244])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | (~spl3_23 | ~spl3_37 | ~spl3_38)),
% 0.21/0.51    inference(equality_resolution,[],[f297])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | (~spl3_23 | ~spl3_37 | ~spl3_38)),
% 0.21/0.51    inference(forward_demodulation,[],[f296,f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0))) ) | (~spl3_23 | ~spl3_37 | ~spl3_38)),
% 0.21/0.51    inference(forward_demodulation,[],[f295,f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0))) ) | (~spl3_37 | ~spl3_38)),
% 0.21/0.51    inference(forward_demodulation,[],[f271,f280])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0))) ) | ~spl3_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    ~spl3_6 | ~spl3_28 | spl3_38 | ~spl3_2 | ~spl3_27 | ~spl3_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f276,f225,f208,f65,f278,f220,f85])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    spl3_28 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl3_27 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    spl3_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_27 | ~spl3_29)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_27 | ~spl3_29)),
% 0.21/0.51    inference(forward_demodulation,[],[f274,f210])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_29),
% 0.21/0.51    inference(resolution,[],[f42,f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f225])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~spl3_35 | ~spl3_36 | spl3_37 | spl3_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f260,f230,f270,f266,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl3_35 <=> v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl3_36 <=> v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    spl3_30 <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v2_funct_1(k5_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),X0)) | ~v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl3_30),
% 0.21/0.51    inference(resolution,[],[f46,f232])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f230])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl3_32 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f242,f165,f85,f65,f244])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | (~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f167,f87,f67,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ~spl3_30 | spl3_18 | ~spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f218,f200,f159,f230])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl3_18 <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl3_25 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_18 | ~spl3_25)),
% 0.21/0.51    inference(backward_demodulation,[],[f161,f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f200])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl3_29 | ~spl3_17 | ~spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f217,f200,f151,f225])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_17 | ~spl3_25)),
% 0.21/0.51    inference(backward_demodulation,[],[f153,f202])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl3_28 | ~spl3_16 | ~spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f216,f200,f145,f220])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl3_16 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_25)),
% 0.21/0.51    inference(backward_demodulation,[],[f147,f202])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl3_25 | ~spl3_11 | ~spl3_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f195,f116,f200])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl3_11 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl3_24 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_11 | ~spl3_24)),
% 0.21/0.51    inference(backward_demodulation,[],[f118,f197])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f195])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl3_24 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f193,f151,f195])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_17),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f153,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl3_23 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f187,f165,f85,f65,f189])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f167,f87,f67,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl3_21 | ~spl3_6 | ~spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f165,f85,f177])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl3_21 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f167,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl3_20 | ~spl3_6 | ~spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f170,f165,f85,f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl3_20 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_19)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f167,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl3_19 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f151,f165])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_17),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f153,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~spl3_18 | ~spl3_9 | spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f157,f124,f104,f159])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl3_12 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_9 | spl3_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f126,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl3_11 | ~spl3_9 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f129,f104,f116])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl3_13 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f131,f106])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl3_17 | ~spl3_9 | ~spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f134,f104,f151])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_9 | ~spl3_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f136,f106])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl3_16 | ~spl3_9 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f139,f104,f145])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl3_15 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_9 | ~spl3_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f141,f106])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f139])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl3_15 | ~spl3_5 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f109,f80,f139])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f82,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl3_14 | ~spl3_4 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f121,f109,f75,f134])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f77,f111])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl3_13 | ~spl3_3 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f109,f70,f129])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f72,f111])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl3_12 | spl3_1 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f109,f60,f124])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl3_1 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f62,f111])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl3_9 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f95,f104])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.51    inference(resolution,[],[f55,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl3_10 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f101,f90,f109])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_7 <=> l1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.21/0.51    inference(resolution,[],[f55,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f95])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ((~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f32,f31,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f90])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f85])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f80])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f75])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f70])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f65])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f60])).
% 0.21/0.51  % (5033)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5032)------------------------------
% 0.21/0.51  % (5032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5032)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5032)Memory used [KB]: 10874
% 0.21/0.51  % (5032)Time elapsed: 0.089 s
% 0.21/0.51  % (5032)------------------------------
% 0.21/0.51  % (5032)------------------------------
% 0.21/0.51  % (5027)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (5025)Success in time 0.148 s
%------------------------------------------------------------------------------
