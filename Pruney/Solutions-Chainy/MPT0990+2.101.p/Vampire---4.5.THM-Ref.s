%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:46 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 368 expanded)
%              Number of leaves         :   40 ( 143 expanded)
%              Depth                    :   22
%              Number of atoms          :  835 (2190 expanded)
%              Number of equality atoms :  213 ( 662 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f194,f204,f210,f294,f301,f311,f357,f397,f436,f799,f1062,f1167])).

fof(f1167,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1166])).

fof(f1166,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f1165])).

fof(f1165,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1164,f308])).

fof(f308,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl4_25
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1164,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1163,f203])).

fof(f203,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1163,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1162,f172])).

fof(f172,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1162,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1161,f132])).

fof(f132,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1161,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f1160])).

fof(f1160,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_54 ),
    inference(superposition,[],[f1032,f798])).

fof(f798,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl4_54
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1032,plain,
    ( ! [X0] :
        ( k6_relat_1(sK0) != k5_relat_1(sK2,X0)
        | k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1031,f354])).

fof(f354,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl4_27
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1031,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1030,f147])).

fof(f147,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1030,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1029,f209])).

fof(f209,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1029,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1028,f187])).

fof(f187,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1028,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2) )
    | ~ spl4_32 ),
    inference(duplicate_literal_removal,[],[f1024])).

fof(f1024,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X0
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_32 ),
    inference(superposition,[],[f403,f435])).

fof(f435,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_32
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f403,plain,(
    ! [X6,X8,X7] :
      ( k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8))
      | k2_funct_1(X6) = X8
      | k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f402,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f402,plain,(
    ! [X6,X8,X7] :
      ( k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6))
      | k2_funct_1(X6) = X8
      | k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f400,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f400,plain,(
    ! [X6,X8,X7] :
      ( k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6))
      | k2_funct_1(X6) = X8
      | k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(k2_funct_1(X6))
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f125,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f125,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

fof(f1062,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f1060])).

fof(f1060,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f177,f162,f794,f344])).

fof(f344,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f114,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f794,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl4_53
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f177,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f799,plain,
    ( ~ spl4_53
    | spl4_54
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f780,f394,f796,f792])).

fof(f394,plain,
    ( spl4_30
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f780,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_30 ),
    inference(resolution,[],[f318,f396])).

fof(f396,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f394])).

fof(f318,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f98,f195])).

fof(f195,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f436,plain,
    ( spl4_32
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f431,f185,f180,f175,f155,f145,f135,f433])).

fof(f135,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f155,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f180,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f431,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f430,f187])).

fof(f430,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f429,f182])).

fof(f182,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f429,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f428,f177])).

fof(f428,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f427,f147])).

fof(f427,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f426,f137])).

fof(f137,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f426,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f423])).

fof(f423,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f406,f157])).

fof(f157,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f406,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f101])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f397,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f392,f191,f185,f175,f170,f160,f394])).

fof(f191,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f392,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f391,f187])).

fof(f391,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f390,f177])).

fof(f390,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f389,f172])).

fof(f389,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f388,f162])).

fof(f388,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f193,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f193,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f357,plain,
    ( spl4_27
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f356,f298,f175,f352])).

fof(f298,plain,
    ( spl4_24
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f356,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f348,f177])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_24 ),
    inference(superposition,[],[f111,f300])).

fof(f300,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f298])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f311,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f310,f291,f160,f306])).

fof(f291,plain,
    ( spl4_23
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f310,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f303,f162])).

fof(f303,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_23 ),
    inference(superposition,[],[f111,f293])).

fof(f293,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f301,plain,
    ( spl4_24
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f296,f180,f175,f135,f298])).

fof(f296,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f295,f137])).

fof(f295,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f286,f182])).

fof(f286,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f91,f177])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f294,plain,
    ( spl4_23
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f289,f165,f160,f140,f291])).

fof(f140,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f165,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f289,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f288,f142])).

fof(f142,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f288,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f285,f167])).

fof(f167,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f285,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f162])).

fof(f210,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f205,f175,f207])).

fof(f205,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f197,f108])).

fof(f108,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f197,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f107,f177])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f204,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f199,f160,f201])).

fof(f199,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f196,f108])).

fof(f196,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f107,f162])).

fof(f194,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f189,f150,f191])).

fof(f150,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f189,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f152,f101])).

fof(f152,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f188,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f68,f185])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f61,f60])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f183,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f69,f180])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f178,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f70,f175])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f173,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f71,f170])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f168,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f72,f165])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f163,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f73,f160])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f158,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f74,f155])).

fof(f74,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f153,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f75,f150])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f148,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f76,f145])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f143,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f77,f140])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f62])).

fof(f138,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f78,f135])).

fof(f78,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f133,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f79,f130])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (28612)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.57  % (28630)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.62/0.57  % (28622)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.62/0.58  % (28621)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.62/0.58  % (28632)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.62/0.58  % (28624)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.62/0.58  % (28637)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.62/0.59  % (28610)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.59  % (28616)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.59  % (28629)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.59  % (28613)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.59  % (28614)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.62/0.60  % (28620)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.62/0.60  % (28626)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.61  % (28638)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.61  % (28617)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.62/0.62  % (28628)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.62/0.62  % (28634)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.62/0.62  % (28611)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.62/0.62  % (28615)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.62/0.62  % (28624)Refutation not found, incomplete strategy% (28624)------------------------------
% 1.62/0.62  % (28624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (28624)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (28624)Memory used [KB]: 2046
% 1.62/0.62  % (28624)Time elapsed: 0.116 s
% 1.62/0.62  % (28624)------------------------------
% 1.62/0.62  % (28624)------------------------------
% 1.62/0.62  % (28635)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.62/0.62  % (28625)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.62/0.62  % (28639)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.62/0.63  % (28626)Refutation not found, incomplete strategy% (28626)------------------------------
% 1.62/0.63  % (28626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.63  % (28626)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.63  
% 1.62/0.63  % (28626)Memory used [KB]: 10746
% 1.62/0.63  % (28626)Time elapsed: 0.200 s
% 1.62/0.63  % (28626)------------------------------
% 1.62/0.63  % (28626)------------------------------
% 1.62/0.63  % (28618)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.62/0.63  % (28636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.63  % (28627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.62/0.63  % (28631)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.62/0.64  % (28619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.62/0.64  % (28623)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.62/0.64  % (28633)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.66  % (28637)Refutation not found, incomplete strategy% (28637)------------------------------
% 1.62/0.66  % (28637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.66  % (28637)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.66  
% 1.62/0.66  % (28637)Memory used [KB]: 6652
% 1.62/0.66  % (28637)Time elapsed: 0.229 s
% 1.62/0.66  % (28637)------------------------------
% 1.62/0.66  % (28637)------------------------------
% 2.38/0.69  % (28634)Refutation not found, incomplete strategy% (28634)------------------------------
% 2.38/0.69  % (28634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.69  % (28634)Termination reason: Refutation not found, incomplete strategy
% 2.38/0.69  
% 2.38/0.69  % (28634)Memory used [KB]: 11001
% 2.38/0.69  % (28634)Time elapsed: 0.266 s
% 2.38/0.69  % (28634)------------------------------
% 2.38/0.69  % (28634)------------------------------
% 2.77/0.75  % (28631)Refutation found. Thanks to Tanya!
% 2.77/0.75  % SZS status Theorem for theBenchmark
% 2.77/0.75  % SZS output start Proof for theBenchmark
% 2.77/0.75  fof(f1168,plain,(
% 2.77/0.75    $false),
% 2.77/0.75    inference(avatar_sat_refutation,[],[f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f194,f204,f210,f294,f301,f311,f357,f397,f436,f799,f1062,f1167])).
% 2.77/0.75  fof(f1167,plain,(
% 2.77/0.75    spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_27 | ~spl4_32 | ~spl4_54),
% 2.77/0.75    inference(avatar_contradiction_clause,[],[f1166])).
% 2.77/0.75  fof(f1166,plain,(
% 2.77/0.75    $false | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(trivial_inequality_removal,[],[f1165])).
% 2.77/0.75  fof(f1165,plain,(
% 2.77/0.75    k6_relat_1(sK1) != k6_relat_1(sK1) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(forward_demodulation,[],[f1164,f308])).
% 2.77/0.75  fof(f308,plain,(
% 2.77/0.75    sK1 = k1_relat_1(sK3) | ~spl4_25),
% 2.77/0.75    inference(avatar_component_clause,[],[f306])).
% 2.77/0.75  fof(f306,plain,(
% 2.77/0.75    spl4_25 <=> sK1 = k1_relat_1(sK3)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.77/0.75  fof(f1164,plain,(
% 2.77/0.75    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1163,f203])).
% 2.77/0.75  fof(f203,plain,(
% 2.77/0.75    v1_relat_1(sK3) | ~spl4_14),
% 2.77/0.75    inference(avatar_component_clause,[],[f201])).
% 2.77/0.75  fof(f201,plain,(
% 2.77/0.75    spl4_14 <=> v1_relat_1(sK3)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.77/0.75  fof(f1163,plain,(
% 2.77/0.75    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1162,f172])).
% 2.77/0.75  fof(f172,plain,(
% 2.77/0.75    v1_funct_1(sK3) | ~spl4_9),
% 2.77/0.75    inference(avatar_component_clause,[],[f170])).
% 2.77/0.75  fof(f170,plain,(
% 2.77/0.75    spl4_9 <=> v1_funct_1(sK3)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.77/0.75  fof(f1162,plain,(
% 2.77/0.75    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1161,f132])).
% 2.77/0.75  fof(f132,plain,(
% 2.77/0.75    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.77/0.75    inference(avatar_component_clause,[],[f130])).
% 2.77/0.75  fof(f130,plain,(
% 2.77/0.75    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.77/0.75  fof(f1161,plain,(
% 2.77/0.75    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(trivial_inequality_removal,[],[f1160])).
% 2.77/0.75  fof(f1160,plain,(
% 2.77/0.75    k6_relat_1(sK0) != k6_relat_1(sK0) | k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27 | ~spl4_32 | ~spl4_54)),
% 2.77/0.75    inference(superposition,[],[f1032,f798])).
% 2.77/0.75  fof(f798,plain,(
% 2.77/0.75    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_54),
% 2.77/0.75    inference(avatar_component_clause,[],[f796])).
% 2.77/0.75  fof(f796,plain,(
% 2.77/0.75    spl4_54 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.77/0.75  fof(f1032,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(sK0) != k5_relat_1(sK2,X0) | k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27 | ~spl4_32)),
% 2.77/0.75    inference(forward_demodulation,[],[f1031,f354])).
% 2.77/0.75  fof(f354,plain,(
% 2.77/0.75    sK0 = k1_relat_1(sK2) | ~spl4_27),
% 2.77/0.75    inference(avatar_component_clause,[],[f352])).
% 2.77/0.75  fof(f352,plain,(
% 2.77/0.75    spl4_27 <=> sK0 = k1_relat_1(sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.77/0.75  fof(f1031,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_32)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1030,f147])).
% 2.77/0.75  fof(f147,plain,(
% 2.77/0.75    v2_funct_1(sK2) | ~spl4_4),
% 2.77/0.75    inference(avatar_component_clause,[],[f145])).
% 2.77/0.75  fof(f145,plain,(
% 2.77/0.75    spl4_4 <=> v2_funct_1(sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.77/0.75  fof(f1030,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_15 | ~spl4_32)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1029,f209])).
% 2.77/0.75  fof(f209,plain,(
% 2.77/0.75    v1_relat_1(sK2) | ~spl4_15),
% 2.77/0.75    inference(avatar_component_clause,[],[f207])).
% 2.77/0.75  fof(f207,plain,(
% 2.77/0.75    spl4_15 <=> v1_relat_1(sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.77/0.75  fof(f1029,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_32)),
% 2.77/0.75    inference(subsumption_resolution,[],[f1028,f187])).
% 2.77/0.75  fof(f187,plain,(
% 2.77/0.75    v1_funct_1(sK2) | ~spl4_12),
% 2.77/0.75    inference(avatar_component_clause,[],[f185])).
% 2.77/0.75  fof(f185,plain,(
% 2.77/0.75    spl4_12 <=> v1_funct_1(sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.77/0.75  fof(f1028,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2)) ) | ~spl4_32),
% 2.77/0.75    inference(duplicate_literal_removal,[],[f1024])).
% 2.77/0.75  fof(f1024,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X0 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_32),
% 2.77/0.75    inference(superposition,[],[f403,f435])).
% 2.77/0.75  fof(f435,plain,(
% 2.77/0.75    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_32),
% 2.77/0.75    inference(avatar_component_clause,[],[f433])).
% 2.77/0.75  fof(f433,plain,(
% 2.77/0.75    spl4_32 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.77/0.75  fof(f403,plain,(
% 2.77/0.75    ( ! [X6,X8,X7] : (k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8)) | k2_funct_1(X6) = X8 | k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6)) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 2.77/0.75    inference(subsumption_resolution,[],[f402,f89])).
% 2.77/0.75  fof(f89,plain,(
% 2.77/0.75    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f39])).
% 2.77/0.75  fof(f39,plain,(
% 2.77/0.75    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.77/0.75    inference(flattening,[],[f38])).
% 2.77/0.75  fof(f38,plain,(
% 2.77/0.75    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.77/0.75    inference(ennf_transformation,[],[f7])).
% 2.77/0.75  fof(f7,axiom,(
% 2.77/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.77/0.75  fof(f402,plain,(
% 2.77/0.75    ( ! [X6,X8,X7] : (k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6)) | k2_funct_1(X6) = X8 | k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8)) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~v1_relat_1(k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 2.77/0.75    inference(subsumption_resolution,[],[f400,f90])).
% 2.77/0.75  fof(f90,plain,(
% 2.77/0.75    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f39])).
% 2.77/0.75  fof(f400,plain,(
% 2.77/0.75    ( ! [X6,X8,X7] : (k5_relat_1(X7,X8) != k6_relat_1(k1_relat_1(X6)) | k2_funct_1(X6) = X8 | k5_relat_1(k2_funct_1(X6),X7) != k6_relat_1(k1_relat_1(X8)) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~v1_funct_1(k2_funct_1(X6)) | ~v1_relat_1(k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 2.77/0.75    inference(superposition,[],[f125,f88])).
% 2.77/0.75  fof(f88,plain,(
% 2.77/0.75    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f37])).
% 2.77/0.75  fof(f37,plain,(
% 2.77/0.75    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.77/0.75    inference(flattening,[],[f36])).
% 2.77/0.75  fof(f36,plain,(
% 2.77/0.75    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.77/0.75    inference(ennf_transformation,[],[f10])).
% 2.77/0.75  fof(f10,axiom,(
% 2.77/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.77/0.75  fof(f125,plain,(
% 2.77/0.75    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.77/0.75    inference(equality_resolution,[],[f104])).
% 2.77/0.75  fof(f104,plain,(
% 2.77/0.75    ( ! [X2,X0,X3,X1] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f50])).
% 2.77/0.75  fof(f50,plain,(
% 2.77/0.75    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.77/0.75    inference(flattening,[],[f49])).
% 2.77/0.75  fof(f49,plain,(
% 2.77/0.75    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.77/0.75    inference(ennf_transformation,[],[f8])).
% 2.77/0.75  fof(f8,axiom,(
% 2.77/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).
% 2.77/0.75  fof(f1062,plain,(
% 2.77/0.75    ~spl4_7 | ~spl4_10 | spl4_53),
% 2.77/0.75    inference(avatar_contradiction_clause,[],[f1060])).
% 2.77/0.75  fof(f1060,plain,(
% 2.77/0.75    $false | (~spl4_7 | ~spl4_10 | spl4_53)),
% 2.77/0.75    inference(unit_resulting_resolution,[],[f177,f162,f794,f344])).
% 2.77/0.75  fof(f344,plain,(
% 2.77/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(duplicate_literal_removal,[],[f343])).
% 2.77/0.75  fof(f343,plain,(
% 2.77/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(superposition,[],[f114,f109])).
% 2.77/0.75  fof(f109,plain,(
% 2.77/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f53])).
% 2.77/0.75  fof(f53,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(flattening,[],[f52])).
% 2.77/0.75  fof(f52,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.77/0.75    inference(ennf_transformation,[],[f16])).
% 2.77/0.75  fof(f16,axiom,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 2.77/0.75  fof(f114,plain,(
% 2.77/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f58])).
% 2.77/0.75  fof(f58,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(flattening,[],[f57])).
% 2.77/0.75  fof(f57,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.77/0.75    inference(ennf_transformation,[],[f13])).
% 2.77/0.75  fof(f13,axiom,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 2.77/0.75  fof(f794,plain,(
% 2.77/0.75    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_53),
% 2.77/0.75    inference(avatar_component_clause,[],[f792])).
% 2.77/0.75  fof(f792,plain,(
% 2.77/0.75    spl4_53 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.77/0.75  fof(f162,plain,(
% 2.77/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.77/0.75    inference(avatar_component_clause,[],[f160])).
% 2.77/0.75  fof(f160,plain,(
% 2.77/0.75    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.77/0.75  fof(f177,plain,(
% 2.77/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.77/0.75    inference(avatar_component_clause,[],[f175])).
% 2.77/0.75  fof(f175,plain,(
% 2.77/0.75    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.77/0.75  fof(f799,plain,(
% 2.77/0.75    ~spl4_53 | spl4_54 | ~spl4_30),
% 2.77/0.75    inference(avatar_split_clause,[],[f780,f394,f796,f792])).
% 2.77/0.75  fof(f394,plain,(
% 2.77/0.75    spl4_30 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.77/0.75  fof(f780,plain,(
% 2.77/0.75    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_30),
% 2.77/0.75    inference(resolution,[],[f318,f396])).
% 2.77/0.75  fof(f396,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_30),
% 2.77/0.75    inference(avatar_component_clause,[],[f394])).
% 2.77/0.75  fof(f318,plain,(
% 2.77/0.75    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.77/0.75    inference(resolution,[],[f98,f195])).
% 2.77/0.75  fof(f195,plain,(
% 2.77/0.75    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.77/0.75    inference(forward_demodulation,[],[f100,f101])).
% 2.77/0.75  fof(f101,plain,(
% 2.77/0.75    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f21])).
% 2.77/0.75  fof(f21,axiom,(
% 2.77/0.75    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.77/0.75  fof(f100,plain,(
% 2.77/0.75    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f26])).
% 2.77/0.75  fof(f26,plain,(
% 2.77/0.75    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.77/0.75    inference(pure_predicate_removal,[],[f19])).
% 2.77/0.75  fof(f19,axiom,(
% 2.77/0.75    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.77/0.75  fof(f98,plain,(
% 2.77/0.75    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f64])).
% 2.77/0.75  fof(f64,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(nnf_transformation,[],[f45])).
% 2.77/0.75  fof(f45,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(flattening,[],[f44])).
% 2.77/0.75  fof(f44,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.77/0.75    inference(ennf_transformation,[],[f17])).
% 2.77/0.75  fof(f17,axiom,(
% 2.77/0.75    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.77/0.75  fof(f436,plain,(
% 2.77/0.75    spl4_32 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.77/0.75    inference(avatar_split_clause,[],[f431,f185,f180,f175,f155,f145,f135,f433])).
% 2.77/0.75  fof(f135,plain,(
% 2.77/0.75    spl4_2 <=> k1_xboole_0 = sK1),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.77/0.75  fof(f155,plain,(
% 2.77/0.75    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.77/0.75  fof(f180,plain,(
% 2.77/0.75    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.77/0.75  fof(f431,plain,(
% 2.77/0.75    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.77/0.75    inference(subsumption_resolution,[],[f430,f187])).
% 2.77/0.75  fof(f430,plain,(
% 2.77/0.75    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.77/0.75    inference(subsumption_resolution,[],[f429,f182])).
% 2.77/0.75  fof(f182,plain,(
% 2.77/0.75    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.77/0.75    inference(avatar_component_clause,[],[f180])).
% 2.77/0.75  fof(f429,plain,(
% 2.77/0.75    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.77/0.75    inference(subsumption_resolution,[],[f428,f177])).
% 2.77/0.75  fof(f428,plain,(
% 2.77/0.75    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.77/0.75    inference(subsumption_resolution,[],[f427,f147])).
% 2.77/0.75  fof(f427,plain,(
% 2.77/0.75    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.77/0.75    inference(subsumption_resolution,[],[f426,f137])).
% 2.77/0.75  fof(f137,plain,(
% 2.77/0.75    k1_xboole_0 != sK1 | spl4_2),
% 2.77/0.75    inference(avatar_component_clause,[],[f135])).
% 2.77/0.75  fof(f426,plain,(
% 2.77/0.75    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.77/0.75    inference(trivial_inequality_removal,[],[f423])).
% 2.77/0.75  fof(f423,plain,(
% 2.77/0.75    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.77/0.75    inference(superposition,[],[f406,f157])).
% 2.77/0.75  fof(f157,plain,(
% 2.77/0.75    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.77/0.75    inference(avatar_component_clause,[],[f155])).
% 2.77/0.75  fof(f406,plain,(
% 2.77/0.75    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.77/0.75    inference(forward_demodulation,[],[f81,f101])).
% 2.77/0.75  fof(f81,plain,(
% 2.77/0.75    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f31])).
% 2.77/0.75  fof(f31,plain,(
% 2.77/0.75    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.77/0.75    inference(flattening,[],[f30])).
% 2.77/0.75  fof(f30,plain,(
% 2.77/0.75    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.77/0.75    inference(ennf_transformation,[],[f23])).
% 2.77/0.75  fof(f23,axiom,(
% 2.77/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.77/0.75  fof(f397,plain,(
% 2.77/0.75    spl4_30 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.77/0.75    inference(avatar_split_clause,[],[f392,f191,f185,f175,f170,f160,f394])).
% 2.77/0.75  fof(f191,plain,(
% 2.77/0.75    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.77/0.75  fof(f392,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.77/0.75    inference(subsumption_resolution,[],[f391,f187])).
% 2.77/0.75  fof(f391,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.77/0.75    inference(subsumption_resolution,[],[f390,f177])).
% 2.77/0.75  fof(f390,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.77/0.75    inference(subsumption_resolution,[],[f389,f172])).
% 2.77/0.75  fof(f389,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.77/0.75    inference(subsumption_resolution,[],[f388,f162])).
% 2.77/0.75  fof(f388,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.77/0.75    inference(superposition,[],[f193,f102])).
% 2.77/0.75  fof(f102,plain,(
% 2.77/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f47])).
% 2.77/0.75  fof(f47,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.77/0.75    inference(flattening,[],[f46])).
% 2.77/0.75  fof(f46,plain,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.77/0.75    inference(ennf_transformation,[],[f20])).
% 2.77/0.75  fof(f20,axiom,(
% 2.77/0.75    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.77/0.75  fof(f193,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.77/0.75    inference(avatar_component_clause,[],[f191])).
% 2.77/0.75  fof(f357,plain,(
% 2.77/0.75    spl4_27 | ~spl4_10 | ~spl4_24),
% 2.77/0.75    inference(avatar_split_clause,[],[f356,f298,f175,f352])).
% 2.77/0.75  fof(f298,plain,(
% 2.77/0.75    spl4_24 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.77/0.75  fof(f356,plain,(
% 2.77/0.75    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_24)),
% 2.77/0.75    inference(subsumption_resolution,[],[f348,f177])).
% 2.77/0.75  fof(f348,plain,(
% 2.77/0.75    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_24),
% 2.77/0.75    inference(superposition,[],[f111,f300])).
% 2.77/0.75  fof(f300,plain,(
% 2.77/0.75    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_24),
% 2.77/0.75    inference(avatar_component_clause,[],[f298])).
% 2.77/0.75  fof(f111,plain,(
% 2.77/0.75    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f55])).
% 2.77/0.75  fof(f55,plain,(
% 2.77/0.75    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(ennf_transformation,[],[f14])).
% 2.77/0.75  fof(f14,axiom,(
% 2.77/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.77/0.75  fof(f311,plain,(
% 2.77/0.75    spl4_25 | ~spl4_7 | ~spl4_23),
% 2.77/0.75    inference(avatar_split_clause,[],[f310,f291,f160,f306])).
% 2.77/0.75  fof(f291,plain,(
% 2.77/0.75    spl4_23 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.77/0.75  fof(f310,plain,(
% 2.77/0.75    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_23)),
% 2.77/0.75    inference(subsumption_resolution,[],[f303,f162])).
% 2.77/0.75  fof(f303,plain,(
% 2.77/0.75    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_23),
% 2.77/0.75    inference(superposition,[],[f111,f293])).
% 2.77/0.75  fof(f293,plain,(
% 2.77/0.75    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_23),
% 2.77/0.75    inference(avatar_component_clause,[],[f291])).
% 2.77/0.75  fof(f301,plain,(
% 2.77/0.75    spl4_24 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.77/0.75    inference(avatar_split_clause,[],[f296,f180,f175,f135,f298])).
% 2.77/0.75  fof(f296,plain,(
% 2.77/0.75    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.77/0.75    inference(subsumption_resolution,[],[f295,f137])).
% 2.77/0.75  fof(f295,plain,(
% 2.77/0.75    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.77/0.75    inference(subsumption_resolution,[],[f286,f182])).
% 2.77/0.75  fof(f286,plain,(
% 2.77/0.75    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.77/0.75    inference(resolution,[],[f91,f177])).
% 2.77/0.75  fof(f91,plain,(
% 2.77/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.77/0.75    inference(cnf_transformation,[],[f63])).
% 2.77/0.75  fof(f63,plain,(
% 2.77/0.75    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(nnf_transformation,[],[f41])).
% 2.77/0.75  fof(f41,plain,(
% 2.77/0.75    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(flattening,[],[f40])).
% 2.77/0.75  fof(f40,plain,(
% 2.77/0.75    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.75    inference(ennf_transformation,[],[f18])).
% 2.77/0.75  fof(f18,axiom,(
% 2.77/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.77/0.75  fof(f294,plain,(
% 2.77/0.75    spl4_23 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.77/0.75    inference(avatar_split_clause,[],[f289,f165,f160,f140,f291])).
% 2.77/0.75  fof(f140,plain,(
% 2.77/0.75    spl4_3 <=> k1_xboole_0 = sK0),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.77/0.75  fof(f165,plain,(
% 2.77/0.75    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.77/0.75  fof(f289,plain,(
% 2.77/0.75    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.77/0.75    inference(subsumption_resolution,[],[f288,f142])).
% 2.77/0.75  fof(f142,plain,(
% 2.77/0.75    k1_xboole_0 != sK0 | spl4_3),
% 2.77/0.75    inference(avatar_component_clause,[],[f140])).
% 2.77/0.75  fof(f288,plain,(
% 2.77/0.75    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.77/0.75    inference(subsumption_resolution,[],[f285,f167])).
% 2.77/0.75  fof(f167,plain,(
% 2.77/0.75    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.77/0.75    inference(avatar_component_clause,[],[f165])).
% 2.77/0.75  fof(f285,plain,(
% 2.77/0.75    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.77/0.75    inference(resolution,[],[f91,f162])).
% 2.77/0.75  fof(f210,plain,(
% 2.77/0.75    spl4_15 | ~spl4_10),
% 2.77/0.75    inference(avatar_split_clause,[],[f205,f175,f207])).
% 2.77/0.75  fof(f205,plain,(
% 2.77/0.75    v1_relat_1(sK2) | ~spl4_10),
% 2.77/0.75    inference(subsumption_resolution,[],[f197,f108])).
% 2.77/0.75  fof(f108,plain,(
% 2.77/0.75    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.77/0.75    inference(cnf_transformation,[],[f4])).
% 2.77/0.75  fof(f4,axiom,(
% 2.77/0.75    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.77/0.75  fof(f197,plain,(
% 2.77/0.75    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.77/0.75    inference(resolution,[],[f107,f177])).
% 2.77/0.75  fof(f107,plain,(
% 2.77/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.77/0.75    inference(cnf_transformation,[],[f51])).
% 2.77/0.75  fof(f51,plain,(
% 2.77/0.75    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.77/0.75    inference(ennf_transformation,[],[f2])).
% 2.77/0.75  fof(f2,axiom,(
% 2.77/0.75    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.77/0.75  fof(f204,plain,(
% 2.77/0.75    spl4_14 | ~spl4_7),
% 2.77/0.75    inference(avatar_split_clause,[],[f199,f160,f201])).
% 2.77/0.75  fof(f199,plain,(
% 2.77/0.75    v1_relat_1(sK3) | ~spl4_7),
% 2.77/0.75    inference(subsumption_resolution,[],[f196,f108])).
% 2.77/0.75  fof(f196,plain,(
% 2.77/0.75    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.77/0.75    inference(resolution,[],[f107,f162])).
% 2.77/0.75  fof(f194,plain,(
% 2.77/0.75    spl4_13 | ~spl4_5),
% 2.77/0.75    inference(avatar_split_clause,[],[f189,f150,f191])).
% 2.77/0.75  fof(f150,plain,(
% 2.77/0.75    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.77/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.77/0.75  fof(f189,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.77/0.75    inference(backward_demodulation,[],[f152,f101])).
% 2.77/0.75  fof(f152,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.77/0.75    inference(avatar_component_clause,[],[f150])).
% 2.77/0.75  fof(f188,plain,(
% 2.77/0.75    spl4_12),
% 2.77/0.75    inference(avatar_split_clause,[],[f68,f185])).
% 2.77/0.75  fof(f68,plain,(
% 2.77/0.75    v1_funct_1(sK2)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f62,plain,(
% 2.77/0.75    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.77/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f61,f60])).
% 2.77/0.75  fof(f60,plain,(
% 2.77/0.75    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.77/0.75    introduced(choice_axiom,[])).
% 2.77/0.75  fof(f61,plain,(
% 2.77/0.75    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.77/0.75    introduced(choice_axiom,[])).
% 2.77/0.75  fof(f29,plain,(
% 2.77/0.75    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.77/0.75    inference(flattening,[],[f28])).
% 2.77/0.75  fof(f28,plain,(
% 2.77/0.75    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.77/0.75    inference(ennf_transformation,[],[f25])).
% 2.77/0.75  fof(f25,negated_conjecture,(
% 2.77/0.75    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.77/0.75    inference(negated_conjecture,[],[f24])).
% 2.77/0.75  fof(f24,conjecture,(
% 2.77/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.77/0.75  fof(f183,plain,(
% 2.77/0.75    spl4_11),
% 2.77/0.75    inference(avatar_split_clause,[],[f69,f180])).
% 2.77/0.75  fof(f69,plain,(
% 2.77/0.75    v1_funct_2(sK2,sK0,sK1)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f178,plain,(
% 2.77/0.75    spl4_10),
% 2.77/0.75    inference(avatar_split_clause,[],[f70,f175])).
% 2.77/0.75  fof(f70,plain,(
% 2.77/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f173,plain,(
% 2.77/0.75    spl4_9),
% 2.77/0.75    inference(avatar_split_clause,[],[f71,f170])).
% 2.77/0.75  fof(f71,plain,(
% 2.77/0.75    v1_funct_1(sK3)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f168,plain,(
% 2.77/0.75    spl4_8),
% 2.77/0.75    inference(avatar_split_clause,[],[f72,f165])).
% 2.77/0.75  fof(f72,plain,(
% 2.77/0.75    v1_funct_2(sK3,sK1,sK0)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f163,plain,(
% 2.77/0.75    spl4_7),
% 2.77/0.75    inference(avatar_split_clause,[],[f73,f160])).
% 2.77/0.75  fof(f73,plain,(
% 2.77/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f158,plain,(
% 2.77/0.75    spl4_6),
% 2.77/0.75    inference(avatar_split_clause,[],[f74,f155])).
% 2.77/0.75  fof(f74,plain,(
% 2.77/0.75    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f153,plain,(
% 2.77/0.75    spl4_5),
% 2.77/0.75    inference(avatar_split_clause,[],[f75,f150])).
% 2.77/0.75  fof(f75,plain,(
% 2.77/0.75    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f148,plain,(
% 2.77/0.75    spl4_4),
% 2.77/0.75    inference(avatar_split_clause,[],[f76,f145])).
% 2.77/0.75  fof(f76,plain,(
% 2.77/0.75    v2_funct_1(sK2)),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f143,plain,(
% 2.77/0.75    ~spl4_3),
% 2.77/0.75    inference(avatar_split_clause,[],[f77,f140])).
% 2.77/0.75  fof(f77,plain,(
% 2.77/0.75    k1_xboole_0 != sK0),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f138,plain,(
% 2.77/0.75    ~spl4_2),
% 2.77/0.75    inference(avatar_split_clause,[],[f78,f135])).
% 2.77/0.75  fof(f78,plain,(
% 2.77/0.75    k1_xboole_0 != sK1),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  fof(f133,plain,(
% 2.77/0.75    ~spl4_1),
% 2.77/0.75    inference(avatar_split_clause,[],[f79,f130])).
% 2.77/0.75  fof(f79,plain,(
% 2.77/0.75    k2_funct_1(sK2) != sK3),
% 2.77/0.75    inference(cnf_transformation,[],[f62])).
% 2.77/0.75  % SZS output end Proof for theBenchmark
% 2.77/0.75  % (28631)------------------------------
% 2.77/0.75  % (28631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.75  % (28631)Termination reason: Refutation
% 2.77/0.75  
% 2.77/0.75  % (28631)Memory used [KB]: 7036
% 2.77/0.75  % (28631)Time elapsed: 0.319 s
% 2.77/0.75  % (28631)------------------------------
% 2.77/0.75  % (28631)------------------------------
% 2.77/0.75  % (28609)Success in time 0.389 s
%------------------------------------------------------------------------------
