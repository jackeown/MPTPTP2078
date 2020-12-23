%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t5_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 637 expanded)
%              Number of leaves         :   63 ( 283 expanded)
%              Depth                    :   10
%              Number of atoms          :  784 (2079 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f566,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f105,f112,f119,f126,f133,f140,f147,f154,f162,f172,f180,f192,f201,f208,f228,f235,f253,f267,f281,f288,f300,f314,f324,f336,f344,f351,f364,f366,f373,f384,f395,f409,f420,f433,f440,f454,f472,f474,f483,f494,f551,f552,f553,f555,f557,f559,f561,f563,f565])).

fof(f565,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f540,f104])).

fof(f104,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f540,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f153,f429])).

fof(f429,plain,
    ( ! [X2,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl6_68
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f153,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f563,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f541,f111])).

fof(f541,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f104,f153,f429])).

fof(f561,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f543,f104])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f77,f429])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',existence_m1_subset_1)).

fof(f559,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f545,f111])).

fof(f545,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f104,f77,f429])).

fof(f557,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f547,f104])).

fof(f547,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f394,f429])).

fof(f394,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl6_62
  <=> m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f555,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f548,f111])).

fof(f548,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f104,f394,f429])).

fof(f553,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_62
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f104,f394,f429])).

fof(f552,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f104,f77,f429])).

fof(f551,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f111,f104,f153,f429])).

fof(f494,plain,
    ( spl6_80
    | spl6_77 ),
    inference(avatar_split_clause,[],[f455,f449,f492])).

fof(f492,plain,
    ( spl6_80
  <=> r2_hidden(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f449,plain,
    ( spl6_77
  <=> ~ v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f455,plain,
    ( r2_hidden(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl6_77 ),
    inference(unit_resulting_resolution,[],[f77,f450,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t2_subset)).

fof(f450,plain,
    ( ~ v1_xboole_0(sK3(sK1))
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f449])).

fof(f483,plain,
    ( ~ spl6_79
    | spl6_51
    | spl6_77 ),
    inference(avatar_split_clause,[],[f457,f449,f334,f481])).

fof(f481,plain,
    ( spl6_79
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f334,plain,
    ( spl6_51
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f457,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl6_51
    | ~ spl6_77 ),
    inference(unit_resulting_resolution,[],[f335,f450,f80])).

fof(f335,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK1))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f334])).

fof(f474,plain,
    ( ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | spl6_65
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f466,f132])).

fof(f132,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_10
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f466,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(backward_demodulation,[],[f462,f408])).

fof(f408,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl6_65
  <=> ~ r2_hidden(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f462,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f111,f125,f153,f432])).

fof(f432,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl6_70
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f125,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_8
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f472,plain,
    ( ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | spl6_19
    | ~ spl6_22
    | spl6_65
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f470,f161])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f470,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f469,f462])).

fof(f469,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f465,f179])).

fof(f179,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_22
  <=> m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f465,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_65
    | ~ spl6_70 ),
    inference(backward_demodulation,[],[f462,f411])).

fof(f411,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_tops_1(sK0,sK1))
    | ~ spl6_65 ),
    inference(resolution,[],[f408,f80])).

fof(f454,plain,
    ( ~ spl6_75
    | spl6_76
    | spl6_31 ),
    inference(avatar_split_clause,[],[f236,f226,f452,f446])).

fof(f446,plain,
    ( spl6_75
  <=> ~ m1_subset_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f452,plain,
    ( spl6_76
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f226,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f236,plain,
    ( v1_xboole_0(sK3(sK1))
    | ~ m1_subset_1(sK1,sK3(sK1))
    | ~ spl6_31 ),
    inference(resolution,[],[f227,f80])).

fof(f227,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f440,plain,
    ( ~ spl6_73
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f425,f418,f438])).

fof(f438,plain,
    ( spl6_73
  <=> ~ v1_xboole_0(k1_tops_1(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f418,plain,
    ( spl6_66
  <=> r2_hidden(sK2,k1_tops_1(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f425,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK4(sK0,sK2)))
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f419,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t7_boole)).

fof(f419,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK4(sK0,sK2)))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f418])).

fof(f433,plain,
    ( spl6_68
    | spl6_70 ),
    inference(avatar_split_clause,[],[f75,f431,f428])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t55_tops_1)).

fof(f420,plain,
    ( spl6_66
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_52
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f396,f393,f342,f138,f110,f103,f96,f418])).

fof(f96,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f138,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f342,plain,
    ( spl6_52
  <=> m1_connsp_2(sK4(sK0,sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f396,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK4(sK0,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_52
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f97,f104,f111,f139,f343,f394,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',d1_connsp_2)).

fof(f343,plain,
    ( m1_connsp_2(sK4(sK0,sK2),sK0,sK2)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f342])).

fof(f139,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f409,plain,
    ( ~ spl6_65
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f399,f152,f145,f138,f110,f103,f96,f407])).

fof(f145,plain,
    ( spl6_15
  <=> ~ m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f399,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f97,f104,f111,f146,f139,f153,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f146,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f395,plain,
    ( spl6_62
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f352,f342,f138,f110,f103,f96,f393])).

fof(f352,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f97,f104,f111,f343,f139,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',dt_m1_connsp_2)).

fof(f384,plain,
    ( spl6_60
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f240,f152,f110,f382])).

fof(f382,plain,
    ( spl6_60
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f240,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f111,f153,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',dt_k1_tops_1)).

fof(f373,plain,
    ( ~ spl6_59
    | spl6_41 ),
    inference(avatar_split_clause,[],[f289,f279,f371])).

fof(f371,plain,
    ( spl6_59
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f279,plain,
    ( spl6_41
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f289,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_41 ),
    inference(unit_resulting_resolution,[],[f77,f280,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t4_subset)).

fof(f280,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f279])).

fof(f366,plain,
    ( ~ spl6_41
    | spl6_36
    | spl6_33 ),
    inference(avatar_split_clause,[],[f237,f233,f251,f279])).

fof(f251,plain,
    ( spl6_36
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f233,plain,
    ( spl6_33
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f237,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl6_33 ),
    inference(resolution,[],[f234,f80])).

fof(f234,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f233])).

fof(f364,plain,
    ( ~ spl6_57
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f355,f349,f362])).

fof(f362,plain,
    ( spl6_57
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f349,plain,
    ( spl6_54
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f355,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f350,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',antisymmetry_r2_hidden)).

fof(f350,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f349])).

fof(f351,plain,
    ( spl6_54
    | spl6_25 ),
    inference(avatar_split_clause,[],[f194,f190,f349])).

fof(f190,plain,
    ( spl6_25
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f194,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f77,f191,f80])).

fof(f191,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f344,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f273,f138,f110,f103,f96,f342])).

fof(f273,plain,
    ( m1_connsp_2(sK4(sK0,sK2),sK0,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f97,f104,f111,f139,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',existence_m1_connsp_2)).

fof(f336,plain,
    ( ~ spl6_51
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f327,f322,f334])).

fof(f322,plain,
    ( spl6_48
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f327,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK1))
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f323,f78])).

fof(f323,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f322])).

fof(f324,plain,
    ( spl6_48
    | spl6_25
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f316,f298,f190,f322])).

fof(f298,plain,
    ( spl6_44
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f316,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl6_25
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f191,f299,f80])).

fof(f299,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f298])).

fof(f314,plain,
    ( ~ spl6_47
    | spl6_35 ),
    inference(avatar_split_clause,[],[f257,f245,f312])).

fof(f312,plain,
    ( spl6_47
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f245,plain,
    ( spl6_35
  <=> ~ m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f257,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f77,f246,f87])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f245])).

fof(f300,plain,
    ( spl6_44
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f216,f199,f152,f298])).

fof(f199,plain,
    ( spl6_26
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f216,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f200,f153,f87])).

fof(f200,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f288,plain,
    ( ~ spl6_43
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f270,f265,f286])).

fof(f286,plain,
    ( spl6_43
  <=> ~ r2_hidden(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f265,plain,
    ( spl6_38
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f270,plain,
    ( ~ r2_hidden(sK2,sK3(sK2))
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f266,f78])).

fof(f266,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f265])).

fof(f281,plain,
    ( ~ spl6_41
    | spl6_33
    | spl6_37 ),
    inference(avatar_split_clause,[],[f256,f248,f233,f279])).

fof(f248,plain,
    ( spl6_37
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f256,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f234,f249,f80])).

fof(f249,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f248])).

fof(f267,plain,
    ( spl6_38
    | spl6_37 ),
    inference(avatar_split_clause,[],[f254,f248,f265])).

fof(f254,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f77,f249,f80])).

fof(f253,plain,
    ( ~ spl6_35
    | spl6_36
    | spl6_21 ),
    inference(avatar_split_clause,[],[f184,f170,f251,f245])).

fof(f170,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f184,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK1,sK2)
    | ~ spl6_21 ),
    inference(resolution,[],[f80,f171])).

fof(f171,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f170])).

fof(f235,plain,
    ( ~ spl6_33
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f219,f206,f233])).

fof(f206,plain,
    ( spl6_28
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f219,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f207,f78])).

fof(f207,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f206])).

fof(f228,plain,
    ( ~ spl6_31
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f212,f199,f226])).

fof(f212,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f200,f78])).

fof(f208,plain,
    ( spl6_28
    | ~ spl6_12
    | spl6_25 ),
    inference(avatar_split_clause,[],[f193,f190,f138,f206])).

fof(f193,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f139,f191,f80])).

fof(f201,plain,
    ( spl6_26
    | spl6_19 ),
    inference(avatar_split_clause,[],[f182,f160,f199])).

fof(f182,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f77,f161,f80])).

fof(f192,plain,
    ( ~ spl6_25
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f185,f152,f131,f190])).

fof(f185,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f132,f153,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t5_subset)).

fof(f180,plain,
    ( spl6_22
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f173,f131,f178])).

fof(f173,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f132,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t1_subset)).

fof(f172,plain,
    ( ~ spl6_21
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f164,f131,f170])).

fof(f164,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f132,f78])).

fof(f162,plain,
    ( ~ spl6_19
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f155,f131,f160])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f132,f86])).

fof(f154,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f67,f152])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    & r2_hidden(sK2,sK1)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_connsp_2(X1,X0,X2)
                & r2_hidden(X2,X1)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X1,sK0,X2)
              & r2_hidden(X2,X1)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X1,X0,X2)
              & r2_hidden(X2,X1)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ m1_connsp_2(sK1,X0,X2)
            & r2_hidden(X2,sK1)
            & v3_pre_topc(sK1,X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_connsp_2(X1,X0,X2)
          & r2_hidden(X2,X1)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ m1_connsp_2(X1,X0,sK2)
        & r2_hidden(sK2,X1)
        & v3_pre_topc(X1,X0)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X1,X0,X2)
              & r2_hidden(X2,X1)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X1,X0,X2)
              & r2_hidden(X2,X1)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r2_hidden(X2,X1)
                    & v3_pre_topc(X1,X0) )
                 => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',t5_connsp_2)).

fof(f147,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f71,f145])).

fof(f71,plain,(
    ~ m1_connsp_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f140,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f68,f138])).

fof(f68,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f133,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f70,f131])).

fof(f70,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f126,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f69,f124])).

fof(f69,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f119,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f89,f117])).

fof(f117,plain,
    ( spl6_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f89,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f62])).

fof(f62,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t5_connsp_2.p',existence_l1_pre_topc)).

fof(f112,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f66,f110])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f65,f103])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f64,f96])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
