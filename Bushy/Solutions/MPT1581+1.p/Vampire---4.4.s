%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t60_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 656 expanded)
%              Number of leaves         :   64 ( 322 expanded)
%              Depth                    :    9
%              Number of atoms          :  678 (3207 expanded)
%              Number of equality atoms :   38 ( 484 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f111,f118,f125,f132,f139,f146,f153,f160,f167,f174,f183,f190,f200,f208,f217,f225,f233,f242,f250,f258,f266,f276,f284,f293,f301,f309,f317,f325,f344,f353,f361,f378,f386,f393,f411,f420,f427,f438,f445,f455,f471,f480,f493,f498,f501])).

fof(f501,plain,
    ( ~ spl9_74
    | ~ spl9_80
    | spl9_85
    | spl9_87 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl9_74
    | ~ spl9_80
    | ~ spl9_85
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f499,f460])).

fof(f460,plain,
    ( m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_74
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f426,f454,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t4_subset)).

fof(f454,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl9_80
  <=> r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f426,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0)))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl9_74
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f499,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_85
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f496,f479])).

fof(f479,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl9_85
  <=> ~ v1_xboole_0(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f496,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_87 ),
    inference(resolution,[],[f492,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t2_subset)).

fof(f492,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl9_87
  <=> ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f498,plain,
    ( ~ spl9_74
    | ~ spl9_80
    | spl9_85
    | spl9_87 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl9_74
    | ~ spl9_80
    | ~ spl9_85
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f495,f460])).

fof(f495,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_85
    | ~ spl9_87 ),
    inference(unit_resulting_resolution,[],[f479,f492,f86])).

fof(f493,plain,
    ( ~ spl9_87
    | ~ spl9_0
    | ~ spl9_10
    | ~ spl9_12
    | spl9_15 ),
    inference(avatar_split_clause,[],[f481,f151,f144,f137,f102,f491])).

fof(f102,plain,
    ( spl9_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f137,plain,
    ( spl9_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f144,plain,
    ( spl9_12
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f151,plain,
    ( spl9_15
  <=> ~ r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f481,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl9_0
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f103,f138,f152,f145,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',d9_orders_2)).

fof(f145,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f152,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f138,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f103,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f102])).

fof(f480,plain,
    ( ~ spl9_85
    | ~ spl9_74
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f461,f453,f425,f478])).

fof(f461,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl9_74
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f426,f454,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t5_subset)).

fof(f471,plain,
    ( ~ spl9_83
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f459,f453,f469])).

fof(f469,plain,
    ( spl9_83
  <=> ~ v1_xboole_0(u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f459,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK1))
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f454,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t7_boole)).

fof(f455,plain,
    ( spl9_80
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f447,f198,f172,f165,f158,f453])).

fof(f158,plain,
    ( spl9_16
  <=> r1_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f165,plain,
    ( spl9_18
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f172,plain,
    ( spl9_20
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f198,plain,
    ( spl9_26
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f447,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f199,f173,f159,f166,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f166,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f159,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f173,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f199,plain,
    ( l1_orders_2(sK1)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f198])).

fof(f445,plain,
    ( spl9_78
    | ~ spl9_2
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f404,f215,f188,f109,f443])).

fof(f443,plain,
    ( spl9_78
  <=> r1_tarski(u1_orders_2(sK6(sK8)),u1_orders_2(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f109,plain,
    ( spl9_2
  <=> l1_orders_2(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f188,plain,
    ( spl9_24
  <=> m1_yellow_0(sK6(sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f215,plain,
    ( spl9_30
  <=> l1_orders_2(sK6(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f404,plain,
    ( r1_tarski(u1_orders_2(sK6(sK8)),u1_orders_2(sK8))
    | ~ spl9_2
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f110,f216,f189,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',d13_yellow_0)).

fof(f189,plain,
    ( m1_yellow_0(sK6(sK8),sK8)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f188])).

fof(f216,plain,
    ( l1_orders_2(sK6(sK8))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f110,plain,
    ( l1_orders_2(sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f438,plain,
    ( spl9_76
    | ~ spl9_2
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f371,f215,f188,f109,f436])).

fof(f436,plain,
    ( spl9_76
  <=> r1_tarski(u1_struct_0(sK6(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f371,plain,
    ( r1_tarski(u1_struct_0(sK6(sK8)),u1_struct_0(sK8))
    | ~ spl9_2
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f110,f216,f189,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f427,plain,
    ( spl9_74
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f412,f409,f425])).

fof(f409,plain,
    ( spl9_70
  <=> r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f412,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0)))
    | ~ spl9_70 ),
    inference(unit_resulting_resolution,[],[f410,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t3_subset)).

fof(f410,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f409])).

fof(f420,plain,
    ( spl9_72
    | ~ spl9_0
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f396,f206,f181,f102,f418])).

fof(f418,plain,
    ( spl9_72
  <=> r1_tarski(u1_orders_2(sK6(sK0)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f181,plain,
    ( spl9_22
  <=> m1_yellow_0(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f206,plain,
    ( spl9_28
  <=> l1_orders_2(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f396,plain,
    ( r1_tarski(u1_orders_2(sK6(sK0)),u1_orders_2(sK0))
    | ~ spl9_0
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f103,f207,f182,f77])).

fof(f182,plain,
    ( m1_yellow_0(sK6(sK0),sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f207,plain,
    ( l1_orders_2(sK6(sK0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f206])).

fof(f411,plain,
    ( spl9_70
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f395,f198,f116,f102,f409])).

fof(f116,plain,
    ( spl9_4
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f395,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f103,f199,f117,f77])).

fof(f117,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f393,plain,
    ( spl9_68
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f379,f376,f391])).

fof(f391,plain,
    ( spl9_68
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f376,plain,
    ( spl9_64
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f379,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_64 ),
    inference(unit_resulting_resolution,[],[f377,f88])).

fof(f377,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f376])).

fof(f386,plain,
    ( spl9_66
    | ~ spl9_0
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f363,f206,f181,f102,f384])).

fof(f384,plain,
    ( spl9_66
  <=> r1_tarski(u1_struct_0(sK6(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f363,plain,
    ( r1_tarski(u1_struct_0(sK6(sK0)),u1_struct_0(sK0))
    | ~ spl9_0
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f103,f207,f182,f76])).

fof(f378,plain,
    ( spl9_64
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f362,f198,f116,f102,f376])).

fof(f362,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f103,f199,f117,f76])).

fof(f361,plain,
    ( spl9_62
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f354,f351,f359])).

fof(f359,plain,
    ( spl9_62
  <=> r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f351,plain,
    ( spl9_60
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f354,plain,
    ( r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl9_60 ),
    inference(unit_resulting_resolution,[],[f352,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f352,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl9_60
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f327,f102,f351])).

fof(f327,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_0 ),
    inference(unit_resulting_resolution,[],[f103,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',dt_u1_orders_2)).

fof(f344,plain,
    ( spl9_58
    | ~ spl9_46
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f326,f323,f282,f342])).

fof(f342,plain,
    ( spl9_58
  <=> l1_orders_2(sK6(sK6(sK6(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f282,plain,
    ( spl9_46
  <=> l1_orders_2(sK6(sK6(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f323,plain,
    ( spl9_56
  <=> m1_yellow_0(sK6(sK6(sK6(sK1))),sK6(sK6(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f326,plain,
    ( l1_orders_2(sK6(sK6(sK6(sK1))))
    | ~ spl9_46
    | ~ spl9_56 ),
    inference(unit_resulting_resolution,[],[f283,f324,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',dt_m1_yellow_0)).

fof(f324,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK1))),sK6(sK6(sK1)))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f323])).

fof(f283,plain,
    ( l1_orders_2(sK6(sK6(sK1)))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f282])).

fof(f325,plain,
    ( spl9_56
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f285,f282,f323])).

fof(f285,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK1))),sK6(sK6(sK1)))
    | ~ spl9_46 ),
    inference(unit_resulting_resolution,[],[f283,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_yellow_0(sK6(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_yellow_0(sK6(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
     => m1_yellow_0(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_yellow_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',existence_m1_yellow_0)).

fof(f317,plain,
    ( spl9_54
    | ~ spl9_42
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f310,f307,f264,f315])).

fof(f315,plain,
    ( spl9_54
  <=> l1_orders_2(sK6(sK6(sK6(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f264,plain,
    ( spl9_42
  <=> l1_orders_2(sK6(sK6(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f307,plain,
    ( spl9_52
  <=> m1_yellow_0(sK6(sK6(sK6(sK8))),sK6(sK6(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f310,plain,
    ( l1_orders_2(sK6(sK6(sK6(sK8))))
    | ~ spl9_42
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f265,f308,f79])).

fof(f308,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK8))),sK6(sK6(sK8)))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f307])).

fof(f265,plain,
    ( l1_orders_2(sK6(sK6(sK8)))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f264])).

fof(f309,plain,
    ( spl9_52
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f267,f264,f307])).

fof(f267,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK8))),sK6(sK6(sK8)))
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f265,f82])).

fof(f301,plain,
    ( spl9_50
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f294,f291,f248,f299])).

fof(f299,plain,
    ( spl9_50
  <=> l1_orders_2(sK6(sK6(sK6(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f248,plain,
    ( spl9_38
  <=> l1_orders_2(sK6(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f291,plain,
    ( spl9_48
  <=> m1_yellow_0(sK6(sK6(sK6(sK0))),sK6(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f294,plain,
    ( l1_orders_2(sK6(sK6(sK6(sK0))))
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(unit_resulting_resolution,[],[f249,f292,f79])).

fof(f292,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK0))),sK6(sK6(sK0)))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f291])).

fof(f249,plain,
    ( l1_orders_2(sK6(sK6(sK0)))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f248])).

fof(f293,plain,
    ( spl9_48
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f251,f248,f291])).

fof(f251,plain,
    ( m1_yellow_0(sK6(sK6(sK6(sK0))),sK6(sK6(sK0)))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f249,f82])).

fof(f284,plain,
    ( spl9_46
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f277,f274,f231,f282])).

fof(f231,plain,
    ( spl9_34
  <=> l1_orders_2(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f274,plain,
    ( spl9_44
  <=> m1_yellow_0(sK6(sK6(sK1)),sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f277,plain,
    ( l1_orders_2(sK6(sK6(sK1)))
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f232,f275,f79])).

fof(f275,plain,
    ( m1_yellow_0(sK6(sK6(sK1)),sK6(sK1))
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f274])).

fof(f232,plain,
    ( l1_orders_2(sK6(sK1))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f231])).

fof(f276,plain,
    ( spl9_44
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f234,f231,f274])).

fof(f234,plain,
    ( m1_yellow_0(sK6(sK6(sK1)),sK6(sK1))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f232,f82])).

fof(f266,plain,
    ( spl9_42
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f259,f256,f215,f264])).

fof(f256,plain,
    ( spl9_40
  <=> m1_yellow_0(sK6(sK6(sK8)),sK6(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f259,plain,
    ( l1_orders_2(sK6(sK6(sK8)))
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f216,f257,f79])).

fof(f257,plain,
    ( m1_yellow_0(sK6(sK6(sK8)),sK6(sK8))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl9_40
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f218,f215,f256])).

fof(f218,plain,
    ( m1_yellow_0(sK6(sK6(sK8)),sK6(sK8))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f216,f82])).

fof(f250,plain,
    ( spl9_38
    | ~ spl9_28
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f243,f240,f206,f248])).

fof(f240,plain,
    ( spl9_36
  <=> m1_yellow_0(sK6(sK6(sK0)),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f243,plain,
    ( l1_orders_2(sK6(sK6(sK0)))
    | ~ spl9_28
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f207,f241,f79])).

fof(f241,plain,
    ( m1_yellow_0(sK6(sK6(sK0)),sK6(sK0))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( spl9_36
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f209,f206,f240])).

fof(f209,plain,
    ( m1_yellow_0(sK6(sK6(sK0)),sK6(sK0))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f207,f82])).

fof(f233,plain,
    ( spl9_34
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f226,f223,f198,f231])).

fof(f223,plain,
    ( spl9_32
  <=> m1_yellow_0(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f226,plain,
    ( l1_orders_2(sK6(sK1))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f199,f224,f79])).

fof(f224,plain,
    ( m1_yellow_0(sK6(sK1),sK1)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl9_32
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f201,f198,f223])).

fof(f201,plain,
    ( m1_yellow_0(sK6(sK1),sK1)
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f199,f82])).

fof(f217,plain,
    ( spl9_30
    | ~ spl9_2
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f193,f188,f109,f215])).

fof(f193,plain,
    ( l1_orders_2(sK6(sK8))
    | ~ spl9_2
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f110,f189,f79])).

fof(f208,plain,
    ( spl9_28
    | ~ spl9_0
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f192,f181,f102,f206])).

fof(f192,plain,
    ( l1_orders_2(sK6(sK0))
    | ~ spl9_0
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f103,f182,f79])).

fof(f200,plain,
    ( spl9_26
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f191,f116,f102,f198])).

fof(f191,plain,
    ( l1_orders_2(sK1)
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f103,f117,f79])).

fof(f190,plain,
    ( spl9_24
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f176,f109,f188])).

fof(f176,plain,
    ( m1_yellow_0(sK6(sK8),sK8)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f110,f82])).

fof(f183,plain,
    ( spl9_22
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f175,f102,f181])).

fof(f175,plain,
    ( m1_yellow_0(sK6(sK0),sK0)
    | ~ spl9_0 ),
    inference(unit_resulting_resolution,[],[f103,f82])).

fof(f174,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f97,f172])).

fof(f97,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f68,f70])).

fof(f70,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK1,sK4,sK5)
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_orders_2(X0,X2,X3)
                            & r1_orders_2(X1,X4,X5)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(sK0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_orders_2(X0,X2,X3)
                        & r1_orders_2(sK1,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X1,X4,X5)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_orders_2(X0,sK2,X3)
                    & r1_orders_2(X1,X4,X5)
                    & X3 = X5
                    & sK2 = X4
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X1,X4,X5)
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_orders_2(X0,X2,sK3)
                & r1_orders_2(X1,X4,X5)
                & sK3 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r1_orders_2(X1,X4,X5)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r1_orders_2(X1,sK4,X5)
            & X3 = X5
            & sK4 = X2
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r1_orders_2(X1,X4,X5)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,X2,X3)
        & r1_orders_2(X1,X4,sK5)
        & sK5 = X3
        & X2 = X4
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X4,X5)
                                & X3 = X5
                                & X2 = X4 )
                             => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',t60_yellow_0)).

fof(f68,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f167,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f96,f165])).

fof(f96,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f69,f71])).

fof(f71,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f53])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f160,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f95,f158])).

fof(f95,plain,(
    r1_orders_2(sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f70,f94])).

fof(f94,plain,(
    r1_orders_2(sK1,sK4,sK3) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f153,plain,(
    ~ spl9_15 ),
    inference(avatar_split_clause,[],[f73,f151])).

fof(f73,plain,(
    ~ r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f146,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f67,f144])).

fof(f67,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f66,f137])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f132,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f71,f130])).

fof(f130,plain,
    ( spl9_8
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f125,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f70,f123])).

fof(f123,plain,
    ( spl9_6
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f118,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f65,f116])).

fof(f65,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f93,f109])).

fof(f93,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    l1_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f62])).

fof(f62,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK8) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t60_yellow_0.p',existence_l1_orders_2)).

fof(f104,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f64,f102])).

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
