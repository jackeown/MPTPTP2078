%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  337 ( 840 expanded)
%              Number of leaves         :   84 ( 388 expanded)
%              Depth                    :   17
%              Number of atoms          : 1708 (5389 expanded)
%              Number of equality atoms :  113 ( 537 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1095,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f184,f190,f195,f258,f263,f275,f286,f298,f302,f322,f327,f329,f439,f443,f452,f468,f525,f547,f551,f555,f559,f564,f593,f609,f611,f632,f633,f691,f709,f711,f855,f856,f858,f859,f875,f896,f898,f936,f955,f956,f1007,f1090,f1091,f1092,f1093,f1094])).

fof(f1094,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1093,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1092,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1091,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1090,plain,
    ( ~ spl5_84
    | ~ spl5_57
    | ~ spl5_69
    | spl5_128 ),
    inference(avatar_split_clause,[],[f1089,f949,f523,f450,f625])).

fof(f625,plain,
    ( spl5_84
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f450,plain,
    ( spl5_57
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f523,plain,
    ( spl5_69
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f949,plain,
    ( spl5_128
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f1089,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_57
    | ~ spl5_69
    | spl5_128 ),
    inference(forward_demodulation,[],[f1088,f524])).

fof(f524,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f523])).

fof(f1088,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_57
    | spl5_128 ),
    inference(forward_demodulation,[],[f1067,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1067,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl5_57
    | spl5_128 ),
    inference(superposition,[],[f950,f451])).

fof(f451,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f450])).

fof(f950,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl5_128 ),
    inference(avatar_component_clause,[],[f949])).

fof(f1007,plain,
    ( spl5_71
    | ~ spl5_1
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f994,f523,f122,f545])).

fof(f545,plain,
    ( spl5_71
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f122,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f994,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_69 ),
    inference(superposition,[],[f128,f524])).

fof(f128,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f956,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_20
    | spl5_15 ),
    inference(avatar_split_clause,[],[f943,f182,f256,f193,f188,f156,f253,f250,f160,f164,f309,f306])).

fof(f306,plain,
    ( spl5_30
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f309,plain,
    ( spl5_31
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f164,plain,
    ( spl5_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f160,plain,
    ( spl5_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f250,plain,
    ( spl5_18
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f253,plain,
    ( spl5_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f156,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f188,plain,
    ( spl5_16
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f193,plain,
    ( spl5_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f256,plain,
    ( spl5_20
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f182,plain,
    ( spl5_15
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f943,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_15 ),
    inference(resolution,[],[f436,f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f436,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f955,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | ~ spl5_61
    | ~ spl5_62
    | ~ spl5_127
    | ~ spl5_128
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_129
    | spl5_15 ),
    inference(avatar_split_clause,[],[f942,f182,f953,f193,f188,f156,f949,f946,f489,f486,f168,f172])).

fof(f172,plain,
    ( spl5_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f168,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f486,plain,
    ( spl5_61
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f489,plain,
    ( spl5_62
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f946,plain,
    ( spl5_127
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f953,plain,
    ( spl5_129
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f942,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f436,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f936,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_72
    | ~ spl5_89
    | ~ spl5_73
    | ~ spl5_123
    | ~ spl5_117
    | ~ spl5_71
    | spl5_88 ),
    inference(avatar_split_clause,[],[f924,f667,f545,f873,f927,f553,f670,f549,f160,f164,f168,f172])).

fof(f549,plain,
    ( spl5_72
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f670,plain,
    ( spl5_89
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f553,plain,
    ( spl5_73
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f927,plain,
    ( spl5_123
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f873,plain,
    ( spl5_117
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f667,plain,
    ( spl5_88
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f924,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_88 ),
    inference(resolution,[],[f668,f119])).

fof(f668,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_88 ),
    inference(avatar_component_clause,[],[f667])).

fof(f898,plain,
    ( ~ spl5_17
    | ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f194,f271])).

fof(f271,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl5_23
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f194,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f896,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_1
    | spl5_20 ),
    inference(avatar_split_clause,[],[f303,f256,f122,f253,f250,f156,f148,f152,f160,f164,f168,f172])).

fof(f152,plain,
    ( spl5_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f148,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f303,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_20 ),
    inference(resolution,[],[f257,f117])).

fof(f257,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f875,plain,
    ( ~ spl5_72
    | ~ spl5_117
    | ~ spl5_88
    | ~ spl5_89
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_11
    | ~ spl5_10
    | spl5_90
    | spl5_71
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f661,f606,f545,f673,f160,f164,f168,f172,f670,f667,f873,f549])).

fof(f673,plain,
    ( spl5_90
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f606,plain,
    ( spl5_82
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2)
        | k1_xboole_0 = X2
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f661,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | spl5_71
    | ~ spl5_82 ),
    inference(resolution,[],[f607,f546])).

fof(f546,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl5_71 ),
    inference(avatar_component_clause,[],[f545])).

fof(f607,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | k1_xboole_0 = X2
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) )
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f606])).

fof(f859,plain,
    ( sK2 != sK3
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f858,plain,
    ( sK2 != sK3
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f856,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f855,plain,
    ( spl5_114
    | ~ spl5_89
    | ~ spl5_72
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f849,f673,f549,f670,f853])).

fof(f853,plain,
    ( spl5_114
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f849,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_72
    | ~ spl5_90 ),
    inference(resolution,[],[f674,f550])).

fof(f550,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f549])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f673])).

fof(f711,plain,
    ( ~ spl5_73
    | spl5_90
    | spl5_94 ),
    inference(avatar_split_clause,[],[f710,f707,f673,f553])).

fof(f707,plain,
    ( spl5_94
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f710,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl5_94 ),
    inference(resolution,[],[f708,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f708,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | spl5_94 ),
    inference(avatar_component_clause,[],[f707])).

fof(f709,plain,
    ( ~ spl5_73
    | ~ spl5_94
    | ~ spl5_84
    | spl5_91 ),
    inference(avatar_split_clause,[],[f705,f689,f625,f707,f553])).

fof(f689,plain,
    ( spl5_91
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f705,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | spl5_91 ),
    inference(forward_demodulation,[],[f704,f112])).

fof(f704,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl5_91 ),
    inference(resolution,[],[f690,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f690,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl5_91 ),
    inference(avatar_component_clause,[],[f689])).

fof(f691,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | ~ spl5_61
    | ~ spl5_62
    | ~ spl5_73
    | ~ spl5_74
    | ~ spl5_75
    | ~ spl5_84
    | ~ spl5_91
    | ~ spl5_57
    | spl5_88 ),
    inference(avatar_split_clause,[],[f685,f667,f450,f689,f625,f562,f557,f553,f489,f486,f168,f172])).

fof(f557,plain,
    ( spl5_74
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f562,plain,
    ( spl5_75
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f685,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f684,f451])).

fof(f684,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(duplicate_literal_removal,[],[f683])).

fof(f683,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f682,f112])).

fof(f682,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f681,f451])).

fof(f681,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f680,f451])).

fof(f680,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f679,f112])).

fof(f679,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_57
    | spl5_88 ),
    inference(forward_demodulation,[],[f677,f451])).

fof(f677,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_88 ),
    inference(resolution,[],[f668,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f633,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f632,plain,
    ( ~ spl5_11
    | ~ spl5_10
    | spl5_61 ),
    inference(avatar_split_clause,[],[f631,f486,f160,f164])).

fof(f631,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl5_61 ),
    inference(resolution,[],[f487,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f487,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f486])).

fof(f611,plain,
    ( ~ spl5_10
    | spl5_81 ),
    inference(avatar_split_clause,[],[f610,f591,f160])).

fof(f591,plain,
    ( spl5_81
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f610,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_81 ),
    inference(resolution,[],[f592,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f592,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl5_81 ),
    inference(avatar_component_clause,[],[f591])).

fof(f609,plain,
    ( spl5_82
    | ~ spl5_73
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f604,f523,f441,f553,f606])).

fof(f441,plain,
    ( spl5_56
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_partfun1(sK2,u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f604,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k1_xboole_0 = X2 )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f603,f524])).

fof(f603,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k1_xboole_0 = X2
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f602,f524])).

fof(f602,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k1_xboole_0 = X2
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f601,f524])).

fof(f601,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f600,f524])).

fof(f600,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK2,X0,X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f599,f524])).

fof(f599,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f598,f524])).

fof(f598,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f597,f524])).

fof(f597,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f594,f524])).

fof(f594,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_56 ),
    inference(resolution,[],[f442,f115])).

fof(f442,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f441])).

fof(f593,plain,
    ( ~ spl5_81
    | spl5_62 ),
    inference(avatar_split_clause,[],[f589,f489,f591])).

fof(f589,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl5_62 ),
    inference(resolution,[],[f490,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f490,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_62 ),
    inference(avatar_component_clause,[],[f489])).

fof(f564,plain,
    ( spl5_75
    | ~ spl5_16
    | ~ spl5_57
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f560,f523,f450,f188,f562])).

fof(f560,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl5_16
    | ~ spl5_57
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f534,f451])).

fof(f534,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_16
    | ~ spl5_69 ),
    inference(superposition,[],[f189,f524])).

fof(f189,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f559,plain,
    ( spl5_74
    | ~ spl5_15
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f533,f523,f182,f557])).

fof(f533,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_15
    | ~ spl5_69 ),
    inference(superposition,[],[f183,f524])).

fof(f183,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f555,plain,
    ( spl5_73
    | ~ spl5_9
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f532,f523,f156,f553])).

fof(f532,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_69 ),
    inference(superposition,[],[f157,f524])).

fof(f157,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f551,plain,
    ( spl5_72
    | ~ spl5_8
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f531,f523,f152,f549])).

fof(f531,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8
    | ~ spl5_69 ),
    inference(superposition,[],[f153,f524])).

fof(f153,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f547,plain,
    ( ~ spl5_71
    | spl5_1
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f529,f523,f122,f545])).

fof(f529,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl5_1
    | ~ spl5_69 ),
    inference(superposition,[],[f123,f524])).

fof(f123,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f525,plain,
    ( spl5_69
    | spl5_22
    | spl5_22
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f520,f466,f176,f267,f267,f523])).

fof(f267,plain,
    ( spl5_22
  <=> ! [X1,X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f176,plain,
    ( spl5_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f466,plain,
    ( spl5_58
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f520,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = sK2 )
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(resolution,[],[f467,f219])).

fof(f219,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X0 )
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f217,f113])).

fof(f113,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f217,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl5_14 ),
    inference(resolution,[],[f216,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f216,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v4_relat_1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X0 )
    | ~ spl5_14 ),
    inference(resolution,[],[f215,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f215,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(X5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v4_relat_1(X0,k1_xboole_0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f213,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f105,f177])).

fof(f177,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f176])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f213,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
      | ~ v4_relat_1(X6,k1_xboole_0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ),
    inference(superposition,[],[f208,f113])).

fof(f208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v4_relat_1(X0,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f206,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f206,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v4_relat_1(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f106,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f467,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f466])).

fof(f468,plain,
    ( spl5_58
    | ~ spl5_17
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f464,f450,f193,f466])).

fof(f464,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_17
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f453,f112])).

fof(f453,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl5_17
    | ~ spl5_57 ),
    inference(superposition,[],[f194,f451])).

fof(f452,plain,
    ( ~ spl5_17
    | spl5_57
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f446,f296,f188,f450,f193])).

fof(f296,plain,
    ( spl5_29
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f446,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(resolution,[],[f297,f189])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f296])).

fof(f443,plain,
    ( ~ spl5_9
    | spl5_56
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f435,f144,f132,f441,f156])).

fof(f132,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f144,plain,
    ( spl5_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f435,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(sK2,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_partfun1(sK2,u1_struct_0(X0))
        | ~ v1_funct_1(sK2) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(sK2,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_partfun1(sK2,u1_struct_0(X0))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f360,f101])).

fof(f360,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(sK2,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f359,f133])).

fof(f133,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(sK2,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f358,f133])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(sK2,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f357,f133])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f356,f133])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f355,f133])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f353,f133])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f120,f145])).

fof(f145,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f439,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_20
    | ~ spl5_19
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f433,f188,f144,f132,f253,f256,f250,f193,f182,f160,f164,f309,f306])).

fof(f433,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(resolution,[],[f360,f189])).

fof(f329,plain,
    ( ~ spl5_12
    | spl5_35 ),
    inference(avatar_split_clause,[],[f328,f325,f168])).

fof(f325,plain,
    ( spl5_35
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f328,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_35 ),
    inference(resolution,[],[f326,f80])).

fof(f326,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f325])).

fof(f327,plain,
    ( ~ spl5_35
    | spl5_31 ),
    inference(avatar_split_clause,[],[f323,f309,f325])).

fof(f323,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_31 ),
    inference(resolution,[],[f310,f93])).

fof(f310,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f309])).

fof(f322,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | spl5_30 ),
    inference(avatar_split_clause,[],[f321,f306,f168,f172])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_30 ),
    inference(resolution,[],[f307,f81])).

fof(f307,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f306])).

fof(f302,plain,
    ( ~ spl5_7
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f149,f268])).

fof(f268,plain,
    ( ! [X2,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f267])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f298,plain,
    ( ~ spl5_9
    | spl5_29
    | spl5_21 ),
    inference(avatar_split_clause,[],[f294,f261,f296,f156])).

fof(f261,plain,
    ( spl5_21
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f294,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ v1_funct_1(sK2) )
    | spl5_21 ),
    inference(resolution,[],[f262,f115])).

fof(f262,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f261])).

fof(f286,plain,
    ( ~ spl5_7
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl5_7
    | spl5_24 ),
    inference(subsumption_resolution,[],[f149,f283])).

fof(f283,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | spl5_24 ),
    inference(resolution,[],[f274,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f274,plain,
    ( ~ v5_relat_1(sK2,u1_struct_0(sK1))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_24
  <=> v5_relat_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f275,plain,
    ( spl5_22
    | spl5_23
    | ~ spl5_24
    | spl5_19 ),
    inference(avatar_split_clause,[],[f264,f253,f273,f270,f267])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_relat_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | spl5_19 ),
    inference(resolution,[],[f254,f209])).

fof(f209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v5_relat_1(X0,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f207,f97])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v5_relat_1(X0,X2)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f107,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f253])).

fof(f263,plain,
    ( ~ spl5_19
    | ~ spl5_9
    | ~ spl5_21
    | spl5_18 ),
    inference(avatar_split_clause,[],[f259,f250,f261,f156,f253])).

fof(f259,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl5_18 ),
    inference(resolution,[],[f251,f101])).

fof(f251,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f258,plain,
    ( ~ spl5_13
    | ~ spl5_12
    | ~ spl5_11
    | ~ spl5_10
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | spl5_1 ),
    inference(avatar_split_clause,[],[f241,f122,f256,f253,f250,f156,f148,f152,f160,f164,f168,f172])).

fof(f241,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f118,f123])).

fof(f195,plain,
    ( spl5_17
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f191,f136,f132,f193])).

fof(f136,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f191,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f137,f133])).

fof(f137,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f190,plain,
    ( spl5_16
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f186,f140,f132,f188])).

fof(f140,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f186,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f141,f133])).

fof(f141,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f184,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f180,f132,f125,f182])).

fof(f125,plain,
    ( spl5_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f180,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f129,f133])).

fof(f129,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f178,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f78,f176])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f174,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f65,f172])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f170,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f66,f168])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f166,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f67,f164])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f162,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f68,f160])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f158,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f69,f156])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f154,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f70,f152])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f150,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f71,f148])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f146,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f72,f144])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f142,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f73,f140])).

fof(f73,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f138,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f74,f136])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f56])).

fof(f134,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f75,f132])).

fof(f75,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f130,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f76,f125,f122])).

fof(f76,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f77,f125,f122])).

fof(f77,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21281)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (21280)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (21278)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (21276)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (21282)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (21289)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (21284)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (21289)Refutation not found, incomplete strategy% (21289)------------------------------
% 0.22/0.49  % (21289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21289)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21289)Memory used [KB]: 1791
% 0.22/0.49  % (21289)Time elapsed: 0.066 s
% 0.22/0.49  % (21289)------------------------------
% 0.22/0.49  % (21289)------------------------------
% 0.22/0.49  % (21291)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (21292)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (21277)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21288)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21296)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (21285)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (21290)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (21279)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (21294)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (21293)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (21279)Refutation not found, incomplete strategy% (21279)------------------------------
% 0.22/0.51  % (21279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21279)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21279)Memory used [KB]: 10746
% 0.22/0.51  % (21279)Time elapsed: 0.086 s
% 0.22/0.51  % (21279)------------------------------
% 0.22/0.51  % (21279)------------------------------
% 0.22/0.51  % (21295)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (21287)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (21277)Refutation not found, incomplete strategy% (21277)------------------------------
% 0.22/0.52  % (21277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21277)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21277)Memory used [KB]: 10746
% 0.22/0.52  % (21277)Time elapsed: 0.077 s
% 0.22/0.52  % (21277)------------------------------
% 0.22/0.52  % (21277)------------------------------
% 0.22/0.52  % (21283)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (21286)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (21296)Refutation not found, incomplete strategy% (21296)------------------------------
% 0.22/0.53  % (21296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21296)Memory used [KB]: 10874
% 0.22/0.53  % (21296)Time elapsed: 0.120 s
% 0.22/0.53  % (21296)------------------------------
% 0.22/0.53  % (21296)------------------------------
% 0.22/0.53  % (21282)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1095,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f127,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f184,f190,f195,f258,f263,f275,f286,f298,f302,f322,f327,f329,f439,f443,f452,f468,f525,f547,f551,f555,f559,f564,f593,f609,f611,f632,f633,f691,f709,f711,f855,f856,f858,f859,f875,f896,f898,f936,f955,f956,f1007,f1090,f1091,f1092,f1093,f1094])).
% 0.22/0.53  fof(f1094,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | sK2 != sK3 | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f1093,plain,(
% 0.22/0.53    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f1092,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | sK2 != sK3 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f1091,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | sK2 != sK3 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f1090,plain,(
% 0.22/0.53    ~spl5_84 | ~spl5_57 | ~spl5_69 | spl5_128),
% 0.22/0.53    inference(avatar_split_clause,[],[f1089,f949,f523,f450,f625])).
% 0.22/0.53  fof(f625,plain,(
% 0.22/0.53    spl5_84 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.22/0.53  fof(f450,plain,(
% 0.22/0.53    spl5_57 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.22/0.53  fof(f523,plain,(
% 0.22/0.53    spl5_69 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 0.22/0.53  fof(f949,plain,(
% 0.22/0.53    spl5_128 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).
% 0.22/0.53  fof(f1089,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_57 | ~spl5_69 | spl5_128)),
% 0.22/0.53    inference(forward_demodulation,[],[f1088,f524])).
% 0.22/0.53  fof(f524,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl5_69),
% 0.22/0.53    inference(avatar_component_clause,[],[f523])).
% 0.22/0.53  fof(f1088,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_57 | spl5_128)),
% 0.22/0.53    inference(forward_demodulation,[],[f1067,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f1067,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl5_57 | spl5_128)),
% 0.22/0.53    inference(superposition,[],[f950,f451])).
% 0.22/0.53  fof(f451,plain,(
% 0.22/0.53    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_57),
% 0.22/0.53    inference(avatar_component_clause,[],[f450])).
% 0.22/0.53  fof(f950,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl5_128),
% 0.22/0.53    inference(avatar_component_clause,[],[f949])).
% 0.22/0.53  fof(f1007,plain,(
% 0.22/0.53    spl5_71 | ~spl5_1 | ~spl5_69),
% 0.22/0.53    inference(avatar_split_clause,[],[f994,f523,f122,f545])).
% 0.22/0.53  fof(f545,plain,(
% 0.22/0.53    spl5_71 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f994,plain,(
% 0.22/0.53    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_1 | ~spl5_69)),
% 0.22/0.53    inference(superposition,[],[f128,f524])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    v5_pre_topc(sK2,sK0,sK1) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f122])).
% 0.22/0.53  fof(f956,plain,(
% 0.22/0.53    ~spl5_30 | ~spl5_31 | ~spl5_11 | ~spl5_10 | ~spl5_18 | ~spl5_19 | ~spl5_9 | ~spl5_16 | ~spl5_17 | ~spl5_20 | spl5_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f943,f182,f256,f193,f188,f156,f253,f250,f160,f164,f309,f306])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    spl5_30 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    spl5_31 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    spl5_11 <=> v2_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl5_10 <=> l1_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    spl5_18 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    spl5_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl5_9 <=> v1_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    spl5_16 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    spl5_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    spl5_20 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    spl5_15 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.53  fof(f943,plain,(
% 0.22/0.53    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_15),
% 0.22/0.53    inference(resolution,[],[f436,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f182])).
% 0.22/0.53  fof(f955,plain,(
% 0.22/0.53    ~spl5_13 | ~spl5_12 | ~spl5_61 | ~spl5_62 | ~spl5_127 | ~spl5_128 | ~spl5_9 | ~spl5_16 | ~spl5_17 | ~spl5_129 | spl5_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f942,f182,f953,f193,f188,f156,f949,f946,f489,f486,f168,f172])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl5_13 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl5_12 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.53  fof(f486,plain,(
% 0.22/0.53    spl5_61 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.22/0.53  fof(f489,plain,(
% 0.22/0.53    spl5_62 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.22/0.53  fof(f946,plain,(
% 0.22/0.53    spl5_127 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).
% 0.22/0.53  fof(f953,plain,(
% 0.22/0.53    spl5_129 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).
% 0.22/0.53  fof(f942,plain,(
% 0.22/0.53    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_15),
% 0.22/0.53    inference(resolution,[],[f436,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 0.22/0.54  fof(f936,plain,(
% 0.22/0.54    ~spl5_13 | ~spl5_12 | ~spl5_11 | ~spl5_10 | ~spl5_72 | ~spl5_89 | ~spl5_73 | ~spl5_123 | ~spl5_117 | ~spl5_71 | spl5_88),
% 0.22/0.54    inference(avatar_split_clause,[],[f924,f667,f545,f873,f927,f553,f670,f549,f160,f164,f168,f172])).
% 0.22/0.54  fof(f549,plain,(
% 0.22/0.54    spl5_72 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 0.22/0.54  fof(f670,plain,(
% 0.22/0.54    spl5_89 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 0.22/0.54  fof(f553,plain,(
% 0.22/0.54    spl5_73 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.22/0.54  fof(f927,plain,(
% 0.22/0.54    spl5_123 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 0.22/0.54  fof(f873,plain,(
% 0.22/0.54    spl5_117 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).
% 0.22/0.54  fof(f667,plain,(
% 0.22/0.54    spl5_88 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 0.22/0.54  fof(f924,plain,(
% 0.22/0.54    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_88),
% 0.22/0.54    inference(resolution,[],[f668,f119])).
% 0.22/0.54  fof(f668,plain,(
% 0.22/0.54    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_88),
% 0.22/0.54    inference(avatar_component_clause,[],[f667])).
% 0.22/0.54  fof(f898,plain,(
% 0.22/0.54    ~spl5_17 | ~spl5_23),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f897])).
% 0.22/0.54  fof(f897,plain,(
% 0.22/0.54    $false | (~spl5_17 | ~spl5_23)),
% 0.22/0.54    inference(subsumption_resolution,[],[f194,f271])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))) ) | ~spl5_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f270])).
% 0.22/0.54  fof(f270,plain,(
% 0.22/0.54    spl5_23 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f193])).
% 0.22/0.54  fof(f896,plain,(
% 0.22/0.54    ~spl5_13 | ~spl5_12 | ~spl5_11 | ~spl5_10 | ~spl5_8 | ~spl5_7 | ~spl5_9 | ~spl5_18 | ~spl5_19 | ~spl5_1 | spl5_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f303,f256,f122,f253,f250,f156,f148,f152,f160,f164,f168,f172])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    spl5_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f303,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_20),
% 0.22/0.54    inference(resolution,[],[f257,f117])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f256])).
% 0.22/0.54  fof(f875,plain,(
% 0.22/0.54    ~spl5_72 | ~spl5_117 | ~spl5_88 | ~spl5_89 | ~spl5_13 | ~spl5_12 | ~spl5_11 | ~spl5_10 | spl5_90 | spl5_71 | ~spl5_82),
% 0.22/0.54    inference(avatar_split_clause,[],[f661,f606,f545,f673,f160,f164,f168,f172,f670,f667,f873,f549])).
% 0.22/0.54  fof(f673,plain,(
% 0.22/0.54    spl5_90 <=> ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 0.22/0.54  fof(f606,plain,(
% 0.22/0.54    spl5_82 <=> ! [X1,X0,X2] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2) | k1_xboole_0 = X2 | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 0.22/0.54  fof(f661,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (spl5_71 | ~spl5_82)),
% 0.22/0.54    inference(resolution,[],[f607,f546])).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl5_71),
% 0.22/0.54    inference(avatar_component_clause,[],[f545])).
% 0.22/0.54  fof(f607,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | k1_xboole_0 = X2 | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2)))) ) | ~spl5_82),
% 0.22/0.54    inference(avatar_component_clause,[],[f606])).
% 0.22/0.54  fof(f859,plain,(
% 0.22/0.54    sK2 != sK3 | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f858,plain,(
% 0.22/0.54    sK2 != sK3 | k1_xboole_0 != u1_struct_0(sK1) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f856,plain,(
% 0.22/0.54    k1_xboole_0 != sK2 | sK2 != sK3 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f855,plain,(
% 0.22/0.54    spl5_114 | ~spl5_89 | ~spl5_72 | ~spl5_90),
% 0.22/0.54    inference(avatar_split_clause,[],[f849,f673,f549,f670,f853])).
% 0.22/0.54  fof(f853,plain,(
% 0.22/0.54    spl5_114 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 0.22/0.54  fof(f849,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | (~spl5_72 | ~spl5_90)),
% 0.22/0.54    inference(resolution,[],[f674,f550])).
% 0.22/0.54  fof(f550,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_72),
% 0.22/0.54    inference(avatar_component_clause,[],[f549])).
% 0.22/0.54  fof(f674,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) | k1_xboole_0 = X0) ) | ~spl5_90),
% 0.22/0.54    inference(avatar_component_clause,[],[f673])).
% 0.22/0.54  fof(f711,plain,(
% 0.22/0.54    ~spl5_73 | spl5_90 | spl5_94),
% 0.22/0.54    inference(avatar_split_clause,[],[f710,f707,f673,f553])).
% 0.22/0.54  fof(f707,plain,(
% 0.22/0.54    spl5_94 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 0.22/0.54  fof(f710,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),X0) | ~v1_funct_1(k1_xboole_0)) ) | spl5_94),
% 0.22/0.54    inference(resolution,[],[f708,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.54  fof(f708,plain,(
% 0.22/0.54    ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | spl5_94),
% 0.22/0.54    inference(avatar_component_clause,[],[f707])).
% 0.22/0.54  fof(f709,plain,(
% 0.22/0.54    ~spl5_73 | ~spl5_94 | ~spl5_84 | spl5_91),
% 0.22/0.54    inference(avatar_split_clause,[],[f705,f689,f625,f707,f553])).
% 0.22/0.54  fof(f689,plain,(
% 0.22/0.54    spl5_91 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 0.22/0.54  fof(f705,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~v1_funct_1(k1_xboole_0) | spl5_91),
% 0.22/0.54    inference(forward_demodulation,[],[f704,f112])).
% 0.22/0.54  fof(f704,plain,(
% 0.22/0.54    ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl5_91),
% 0.22/0.54    inference(resolution,[],[f690,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.22/0.54  fof(f690,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | spl5_91),
% 0.22/0.54    inference(avatar_component_clause,[],[f689])).
% 0.22/0.54  fof(f691,plain,(
% 0.22/0.54    ~spl5_13 | ~spl5_12 | ~spl5_61 | ~spl5_62 | ~spl5_73 | ~spl5_74 | ~spl5_75 | ~spl5_84 | ~spl5_91 | ~spl5_57 | spl5_88),
% 0.22/0.54    inference(avatar_split_clause,[],[f685,f667,f450,f689,f625,f562,f557,f553,f489,f486,f168,f172])).
% 0.22/0.54  fof(f557,plain,(
% 0.22/0.54    spl5_74 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.22/0.54  fof(f562,plain,(
% 0.22/0.54    spl5_75 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 0.22/0.54  fof(f685,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f684,f451])).
% 0.22/0.54  fof(f684,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f683])).
% 0.22/0.54  fof(f683,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f682,f112])).
% 0.22/0.54  fof(f682,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f681,f451])).
% 0.22/0.54  fof(f681,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f680,f451])).
% 0.22/0.54  fof(f680,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f679,f112])).
% 0.22/0.54  fof(f679,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_57 | spl5_88)),
% 0.22/0.54    inference(forward_demodulation,[],[f677,f451])).
% 0.22/0.54  fof(f677,plain,(
% 0.22/0.54    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_88),
% 0.22/0.54    inference(resolution,[],[f668,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f633,plain,(
% 0.22/0.54    k1_xboole_0 != sK2 | sK2 != sK3 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f632,plain,(
% 0.22/0.54    ~spl5_11 | ~spl5_10 | spl5_61),
% 0.22/0.54    inference(avatar_split_clause,[],[f631,f486,f160,f164])).
% 0.22/0.54  fof(f631,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl5_61),
% 0.22/0.54    inference(resolution,[],[f487,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.22/0.54  fof(f487,plain,(
% 0.22/0.54    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_61),
% 0.22/0.54    inference(avatar_component_clause,[],[f486])).
% 0.22/0.54  fof(f611,plain,(
% 0.22/0.54    ~spl5_10 | spl5_81),
% 0.22/0.54    inference(avatar_split_clause,[],[f610,f591,f160])).
% 0.22/0.54  fof(f591,plain,(
% 0.22/0.54    spl5_81 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 0.22/0.54  fof(f610,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | spl5_81),
% 0.22/0.54    inference(resolution,[],[f592,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.54  fof(f592,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl5_81),
% 0.22/0.54    inference(avatar_component_clause,[],[f591])).
% 0.22/0.54  fof(f609,plain,(
% 0.22/0.54    spl5_82 | ~spl5_73 | ~spl5_56 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f604,f523,f441,f553,f606])).
% 0.22/0.54  fof(f441,plain,(
% 0.22/0.54    spl5_56 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_partfun1(sK2,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.22/0.54  fof(f604,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | k1_xboole_0 = X2) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f603,f524])).
% 0.22/0.54  fof(f603,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | k1_xboole_0 = X2 | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f602,f524])).
% 0.22/0.54  fof(f602,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | k1_xboole_0 = X2 | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f601,f524])).
% 0.22/0.54  fof(f601,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f600,f524])).
% 0.22/0.54  fof(f600,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK2,X0,X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f599,f524])).
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f598,f524])).
% 0.22/0.54  fof(f598,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f597,f524])).
% 0.22/0.54  fof(f597,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | (~spl5_56 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f594,f524])).
% 0.22/0.54  fof(f594,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | k1_xboole_0 = X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X2))) | ~v1_funct_2(sK2,u1_struct_0(X0),X2) | ~v1_funct_1(sK2)) ) | ~spl5_56),
% 0.22/0.54    inference(resolution,[],[f442,f115])).
% 0.22/0.54  fof(f442,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_partfun1(sK2,u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1)) ) | ~spl5_56),
% 0.22/0.54    inference(avatar_component_clause,[],[f441])).
% 0.22/0.54  fof(f593,plain,(
% 0.22/0.54    ~spl5_81 | spl5_62),
% 0.22/0.54    inference(avatar_split_clause,[],[f589,f489,f591])).
% 0.22/0.54  fof(f589,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl5_62),
% 0.22/0.54    inference(resolution,[],[f490,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.22/0.54  fof(f490,plain,(
% 0.22/0.54    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_62),
% 0.22/0.54    inference(avatar_component_clause,[],[f489])).
% 0.22/0.54  fof(f564,plain,(
% 0.22/0.54    spl5_75 | ~spl5_16 | ~spl5_57 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f560,f523,f450,f188,f562])).
% 0.22/0.54  fof(f560,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl5_16 | ~spl5_57 | ~spl5_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f534,f451])).
% 0.22/0.54  fof(f534,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_16 | ~spl5_69)),
% 0.22/0.54    inference(superposition,[],[f189,f524])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f188])).
% 0.22/0.54  fof(f559,plain,(
% 0.22/0.54    spl5_74 | ~spl5_15 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f533,f523,f182,f557])).
% 0.22/0.54  fof(f533,plain,(
% 0.22/0.54    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_15 | ~spl5_69)),
% 0.22/0.54    inference(superposition,[],[f183,f524])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f182])).
% 0.22/0.54  fof(f555,plain,(
% 0.22/0.54    spl5_73 | ~spl5_9 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f532,f523,f156,f553])).
% 0.22/0.54  fof(f532,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0) | (~spl5_9 | ~spl5_69)),
% 0.22/0.54    inference(superposition,[],[f157,f524])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl5_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f156])).
% 0.22/0.54  fof(f551,plain,(
% 0.22/0.54    spl5_72 | ~spl5_8 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f531,f523,f152,f549])).
% 0.22/0.54  fof(f531,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_8 | ~spl5_69)),
% 0.22/0.54    inference(superposition,[],[f153,f524])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f152])).
% 0.22/0.54  fof(f547,plain,(
% 0.22/0.54    ~spl5_71 | spl5_1 | ~spl5_69),
% 0.22/0.54    inference(avatar_split_clause,[],[f529,f523,f122,f545])).
% 0.22/0.54  fof(f529,plain,(
% 0.22/0.54    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl5_1 | ~spl5_69)),
% 0.22/0.54    inference(superposition,[],[f123,f524])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,sK0,sK1) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f122])).
% 0.22/0.54  fof(f525,plain,(
% 0.22/0.54    spl5_69 | spl5_22 | spl5_22 | ~spl5_14 | ~spl5_58),
% 0.22/0.54    inference(avatar_split_clause,[],[f520,f466,f176,f267,f267,f523])).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    spl5_22 <=> ! [X1,X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    spl5_14 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.54  fof(f466,plain,(
% 0.22/0.54    spl5_58 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.22/0.54  fof(f520,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK2) ) | (~spl5_14 | ~spl5_58)),
% 0.22/0.54    inference(resolution,[],[f467,f219])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X0) ) | ~spl5_14),
% 0.22/0.54    inference(forward_demodulation,[],[f217,f113])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f64])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f216,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~v4_relat_1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) ) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f215,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X5,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v4_relat_1(X0,k1_xboole_0)) ) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f213,f196])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f105,f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0) | ~spl5_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f176])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X5,X9] : (m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v4_relat_1(X6,k1_xboole_0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) )),
% 0.22/0.54    inference(superposition,[],[f208,f113])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v4_relat_1(X0,X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.22/0.54    inference(resolution,[],[f206,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v4_relat_1(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.54    inference(resolution,[],[f106,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.54    inference(flattening,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.22/0.54  fof(f467,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_58),
% 0.22/0.54    inference(avatar_component_clause,[],[f466])).
% 0.22/0.54  fof(f468,plain,(
% 0.22/0.54    spl5_58 | ~spl5_17 | ~spl5_57),
% 0.22/0.54    inference(avatar_split_clause,[],[f464,f450,f193,f466])).
% 0.22/0.54  fof(f464,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_17 | ~spl5_57)),
% 0.22/0.54    inference(forward_demodulation,[],[f453,f112])).
% 0.22/0.54  fof(f453,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl5_17 | ~spl5_57)),
% 0.22/0.54    inference(superposition,[],[f194,f451])).
% 0.22/0.54  fof(f452,plain,(
% 0.22/0.54    ~spl5_17 | spl5_57 | ~spl5_16 | ~spl5_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f446,f296,f188,f450,f193])).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    spl5_29 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_16 | ~spl5_29)),
% 0.22/0.54    inference(resolution,[],[f297,f189])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))) ) | ~spl5_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f296])).
% 0.22/0.54  fof(f443,plain,(
% 0.22/0.54    ~spl5_9 | spl5_56 | ~spl5_3 | ~spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f435,f144,f132,f441,f156])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl5_3 <=> sK2 = sK3),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    spl5_6 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f435,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(sK2,X0,X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_partfun1(sK2,u1_struct_0(X0)) | ~v1_funct_1(sK2)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f434])).
% 0.22/0.54  fof(f434,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(sK2,X0,X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_partfun1(sK2,u1_struct_0(X0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(resolution,[],[f360,f101])).
% 0.22/0.54  fof(f360,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(sK2,X0,X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f359,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    sK2 = sK3 | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(sK2,X0,X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f358,f133])).
% 0.22/0.54  fof(f358,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v5_pre_topc(sK2,X0,X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f357,f133])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f356,f133])).
% 0.22/0.54  fof(f356,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f355,f133])).
% 0.22/0.54  fof(f355,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f353,f133])).
% 0.22/0.54  fof(f353,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_6),
% 0.22/0.54    inference(resolution,[],[f120,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    v1_funct_1(sK3) | ~spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f144])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f57])).
% 0.22/0.54  fof(f439,plain,(
% 0.22/0.54    ~spl5_30 | ~spl5_31 | ~spl5_11 | ~spl5_10 | ~spl5_15 | ~spl5_17 | ~spl5_18 | spl5_20 | ~spl5_19 | ~spl5_3 | ~spl5_6 | ~spl5_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f433,f188,f144,f132,f253,f256,f250,f193,f182,f160,f164,f309,f306])).
% 0.22/0.54  fof(f433,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_3 | ~spl5_6 | ~spl5_16)),
% 0.22/0.54    inference(resolution,[],[f360,f189])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    ~spl5_12 | spl5_35),
% 0.22/0.54    inference(avatar_split_clause,[],[f328,f325,f168])).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    spl5_35 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | spl5_35),
% 0.22/0.54    inference(resolution,[],[f326,f80])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f325])).
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    ~spl5_35 | spl5_31),
% 0.22/0.54    inference(avatar_split_clause,[],[f323,f309,f325])).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_31),
% 0.22/0.54    inference(resolution,[],[f310,f93])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f309])).
% 0.22/0.54  fof(f322,plain,(
% 0.22/0.54    ~spl5_13 | ~spl5_12 | spl5_30),
% 0.22/0.54    inference(avatar_split_clause,[],[f321,f306,f168,f172])).
% 0.22/0.54  fof(f321,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_30),
% 0.22/0.54    inference(resolution,[],[f307,f81])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f306])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    ~spl5_7 | ~spl5_22),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f300])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    $false | (~spl5_7 | ~spl5_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f268])).
% 0.22/0.54  fof(f268,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl5_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f267])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f148])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    ~spl5_9 | spl5_29 | spl5_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f294,f261,f296,f156])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    spl5_21 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) | ~v1_funct_1(sK2)) ) | spl5_21),
% 0.22/0.54    inference(resolution,[],[f262,f115])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | spl5_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f261])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ~spl5_7 | spl5_24),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f285])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    $false | (~spl5_7 | spl5_24)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f283])).
% 0.22/0.54  fof(f283,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))) ) | spl5_24),
% 0.22/0.54    inference(resolution,[],[f274,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    ~v5_relat_1(sK2,u1_struct_0(sK1)) | spl5_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f273])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    spl5_24 <=> v5_relat_1(sK2,u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    spl5_22 | spl5_23 | ~spl5_24 | spl5_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f264,f253,f273,f270,f267])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_relat_1(sK2,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | spl5_19),
% 0.22/0.54    inference(resolution,[],[f254,f209])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v5_relat_1(X0,X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.22/0.54    inference(resolution,[],[f207,f97])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v5_relat_1(X0,X2) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.54    inference(resolution,[],[f107,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.54    inference(flattening,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl5_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f253])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    ~spl5_19 | ~spl5_9 | ~spl5_21 | spl5_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f259,f250,f261,f156,f253])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl5_18),
% 0.22/0.54    inference(resolution,[],[f251,f101])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl5_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f250])).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    ~spl5_13 | ~spl5_12 | ~spl5_11 | ~spl5_10 | ~spl5_8 | ~spl5_7 | ~spl5_9 | ~spl5_18 | ~spl5_19 | ~spl5_20 | spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f241,f122,f256,f253,f250,f156,f148,f152,f160,f164,f168,f172])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_1),
% 0.22/0.54    inference(resolution,[],[f118,f123])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    spl5_17 | ~spl5_3 | ~spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f191,f136,f132,f193])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_3 | ~spl5_4)),
% 0.22/0.54    inference(superposition,[],[f137,f133])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f136])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    spl5_16 | ~spl5_3 | ~spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f186,f140,f132,f188])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    spl5_5 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_3 | ~spl5_5)),
% 0.22/0.54    inference(superposition,[],[f141,f133])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f140])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    spl5_15 | ~spl5_2 | ~spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f180,f132,f125,f182])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    spl5_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3)),
% 0.22/0.54    inference(forward_demodulation,[],[f129,f133])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f125])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    spl5_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f78,f176])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl5_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f65,f172])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54,f53,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f20])).
% 0.22/0.54  fof(f20,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl5_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f66,f168])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    spl5_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f67,f164])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    v2_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl5_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f68,f160])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    spl5_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f69,f156])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    spl5_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f70,f152])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    spl5_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f71,f148])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f144])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f73,f140])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f74,f136])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f75,f132])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    sK2 = sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f76,f125,f122])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f77,f125,f122])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (21282)------------------------------
% 0.22/0.54  % (21282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21282)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (21282)Memory used [KB]: 11641
% 0.22/0.54  % (21282)Time elapsed: 0.116 s
% 0.22/0.54  % (21282)------------------------------
% 0.22/0.54  % (21282)------------------------------
% 0.22/0.54  % (21275)Success in time 0.177 s
%------------------------------------------------------------------------------
