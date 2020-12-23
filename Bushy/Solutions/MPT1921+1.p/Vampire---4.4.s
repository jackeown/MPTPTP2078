%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t19_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 733 expanded)
%              Number of leaves         :   73 ( 315 expanded)
%              Depth                    :    9
%              Number of atoms          :  786 (2004 expanded)
%              Number of equality atoms :    6 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f620,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f138,f145,f152,f159,f167,f174,f185,f192,f199,f206,f214,f223,f231,f242,f251,f259,f271,f280,f288,f295,f305,f313,f321,f331,f339,f347,f361,f369,f377,f384,f391,f398,f405,f426,f434,f447,f457,f465,f483,f512,f519,f529,f536,f548,f550,f552,f554,f556,f560,f573,f575,f585,f593,f607,f609,f611,f613,f615,f617])).

fof(f617,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f599,f482])).

fof(f482,plain,
    ( ~ m1_yellow_0(sK2,sK1)
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl9_81
  <=> ~ m1_yellow_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f599,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f130,f151,f508,f158,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',d8_yellow_6)).

fof(f158,plain,
    ( m1_yellow_6(sK2,sK0,sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_8
  <=> m1_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f508,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl9_82
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f151,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl9_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f130,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f615,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f600,f158])).

fof(f600,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f130,f151,f508,f482,f100])).

fof(f613,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f601,f508])).

fof(f601,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81 ),
    inference(unit_resulting_resolution,[],[f130,f151,f158,f482,f100])).

fof(f611,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f602,f151])).

fof(f602,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f130,f508,f158,f482,f100])).

fof(f609,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f603,f130])).

fof(f603,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f151,f508,f158,f482,f100])).

fof(f607,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_81
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_81
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f130,f151,f508,f158,f482,f100])).

fof(f593,plain,
    ( spl9_94
    | ~ spl9_78
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f586,f583,f472,f591])).

fof(f591,plain,
    ( spl9_94
  <=> l1_orders_2(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f472,plain,
    ( spl9_78
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f583,plain,
    ( spl9_92
  <=> m1_yellow_0(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f586,plain,
    ( l1_orders_2(sK3(sK2))
    | ~ spl9_78
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f473,f584,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',dt_m1_yellow_0)).

fof(f584,plain,
    ( m1_yellow_0(sK3(sK2),sK2)
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f583])).

fof(f473,plain,
    ( l1_orders_2(sK2)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f472])).

fof(f585,plain,
    ( spl9_92
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f566,f472,f583])).

fof(f566,plain,
    ( m1_yellow_0(sK3(sK2),sK2)
    | ~ spl9_78 ),
    inference(unit_resulting_resolution,[],[f473,f103])).

fof(f103,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
     => m1_yellow_0(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_yellow_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',existence_m1_yellow_0)).

fof(f575,plain,
    ( spl9_82
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f562,f157,f150,f129,f507])).

fof(f562,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f561,f130])).

fof(f561,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f545,f151])).

fof(f545,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl9_8 ),
    inference(resolution,[],[f112,f158])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',dt_m1_yellow_6)).

fof(f573,plain,
    ( spl9_90
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f563,f472,f571])).

fof(f571,plain,
    ( spl9_90
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f563,plain,
    ( l1_struct_0(sK2)
    | ~ spl9_78 ),
    inference(unit_resulting_resolution,[],[f473,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',dt_l1_orders_2)).

fof(f560,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f558,f130])).

fof(f558,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f557,f151])).

fof(f557,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f545,f511])).

fof(f511,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ spl9_83 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl9_83
  <=> ~ l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f556,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f537,f158])).

fof(f537,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_83 ),
    inference(unit_resulting_resolution,[],[f130,f151,f511,f112])).

fof(f554,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f541,f511])).

fof(f541,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f130,f151,f158,f112])).

fof(f552,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f542,f151])).

fof(f542,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(unit_resulting_resolution,[],[f130,f511,f158,f112])).

fof(f550,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f543,f130])).

fof(f543,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(unit_resulting_resolution,[],[f151,f511,f158,f112])).

fof(f548,plain,
    ( ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_83 ),
    inference(unit_resulting_resolution,[],[f130,f151,f511,f158,f112])).

fof(f536,plain,
    ( ~ spl9_89
    | ~ spl9_2
    | spl9_79 ),
    inference(avatar_split_clause,[],[f503,f475,f136,f534])).

fof(f534,plain,
    ( spl9_89
  <=> ~ m1_yellow_0(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f136,plain,
    ( spl9_2
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f475,plain,
    ( spl9_79
  <=> ~ l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f503,plain,
    ( ~ m1_yellow_0(sK2,sK7)
    | ~ spl9_2
    | ~ spl9_79 ),
    inference(unit_resulting_resolution,[],[f137,f476,f98])).

fof(f476,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f475])).

fof(f137,plain,
    ( l1_orders_2(sK7)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f529,plain,
    ( ~ spl9_87
    | ~ spl9_4
    | spl9_79 ),
    inference(avatar_split_clause,[],[f494,f475,f143,f527])).

fof(f527,plain,
    ( spl9_87
  <=> ~ l1_waybel_0(sK2,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f143,plain,
    ( spl9_4
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f494,plain,
    ( ~ l1_waybel_0(sK2,sK8)
    | ~ spl9_4
    | ~ spl9_79 ),
    inference(unit_resulting_resolution,[],[f144,f476,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',dt_l1_waybel_0)).

fof(f144,plain,
    ( l1_struct_0(sK8)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f519,plain,
    ( ~ spl9_85
    | ~ spl9_10
    | spl9_79 ),
    inference(avatar_split_clause,[],[f493,f475,f165,f517])).

fof(f517,plain,
    ( spl9_85
  <=> ~ l1_waybel_0(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f165,plain,
    ( spl9_10
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f493,plain,
    ( ~ l1_waybel_0(sK2,sK7)
    | ~ spl9_10
    | ~ spl9_79 ),
    inference(unit_resulting_resolution,[],[f166,f476,f99])).

fof(f166,plain,
    ( l1_struct_0(sK7)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f512,plain,
    ( ~ spl9_83
    | ~ spl9_0
    | spl9_79 ),
    inference(avatar_split_clause,[],[f484,f475,f129,f510])).

fof(f484,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ spl9_0
    | ~ spl9_79 ),
    inference(unit_resulting_resolution,[],[f130,f476,f99])).

fof(f483,plain,
    ( ~ spl9_79
    | ~ spl9_81
    | spl9_13
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f470,f240,f172,f481,f475])).

fof(f172,plain,
    ( spl9_13
  <=> ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f240,plain,
    ( spl9_28
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f470,plain,
    ( ~ m1_yellow_0(sK2,sK1)
    | ~ l1_orders_2(sK2)
    | ~ spl9_13
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f469,f241])).

fof(f241,plain,
    ( l1_orders_2(sK1)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f469,plain,
    ( ~ m1_yellow_0(sK2,sK1)
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl9_13 ),
    inference(resolution,[],[f95,f173])).

fof(f173,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',d13_yellow_0)).

fof(f465,plain,
    ( spl9_76
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f436,f150,f129,f463])).

fof(f463,plain,
    ( spl9_76
  <=> m1_yellow_6(sK6(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f436,plain,
    ( m1_yellow_6(sK6(sK0,sK1),sK0,sK1)
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f130,f151,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_yellow_6(sK6(X0,X1),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_yellow_6(sK6(X0,X1),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_yellow_6(X2,X0,X1)
     => m1_yellow_6(sK6(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ? [X2] : m1_yellow_6(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',existence_m1_yellow_6)).

fof(f457,plain,
    ( spl9_74
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f450,f445,f455])).

fof(f455,plain,
    ( spl9_74
  <=> l1_struct_0(sK3(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f445,plain,
    ( spl9_72
  <=> l1_orders_2(sK3(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f450,plain,
    ( l1_struct_0(sK3(sK4(sK0)))
    | ~ spl9_72 ),
    inference(unit_resulting_resolution,[],[f446,f93])).

fof(f446,plain,
    ( l1_orders_2(sK3(sK4(sK0)))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f445])).

fof(f447,plain,
    ( spl9_72
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f435,f432,f257,f445])).

fof(f257,plain,
    ( spl9_32
  <=> l1_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f432,plain,
    ( spl9_70
  <=> m1_yellow_0(sK3(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f435,plain,
    ( l1_orders_2(sK3(sK4(sK0)))
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(unit_resulting_resolution,[],[f258,f433,f98])).

fof(f433,plain,
    ( m1_yellow_0(sK3(sK4(sK0)),sK4(sK0))
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f432])).

fof(f258,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f257])).

fof(f434,plain,
    ( spl9_70
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f263,f257,f432])).

fof(f263,plain,
    ( m1_yellow_0(sK3(sK4(sK0)),sK4(sK0))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f258,f103])).

fof(f426,plain,
    ( ~ spl9_69
    | spl9_67 ),
    inference(avatar_split_clause,[],[f416,f403,f424])).

fof(f424,plain,
    ( spl9_69
  <=> ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f403,plain,
    ( spl9_67
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f416,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_67 ),
    inference(unit_resulting_resolution,[],[f404,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',t1_subset)).

fof(f404,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f403])).

fof(f405,plain,
    ( ~ spl9_67
    | spl9_13 ),
    inference(avatar_split_clause,[],[f260,f172,f403])).

fof(f260,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f173,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',t3_subset)).

fof(f398,plain,
    ( spl9_64
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f350,f337,f249,f396])).

fof(f396,plain,
    ( spl9_64
  <=> v1_funct_1(u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f249,plain,
    ( spl9_30
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f337,plain,
    ( spl9_50
  <=> l1_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f350,plain,
    ( v1_funct_1(u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(unit_resulting_resolution,[],[f250,f338,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',dt_u1_waybel_0)).

fof(f338,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f337])).

fof(f250,plain,
    ( l1_struct_0(sK1)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f249])).

fof(f391,plain,
    ( spl9_62
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f351,f204,f165,f389])).

fof(f389,plain,
    ( spl9_62
  <=> v1_funct_1(u1_waybel_0(sK7,sK4(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f204,plain,
    ( spl9_20
  <=> l1_waybel_0(sK4(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f351,plain,
    ( v1_funct_1(u1_waybel_0(sK7,sK4(sK7)))
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f166,f205,f110])).

fof(f205,plain,
    ( l1_waybel_0(sK4(sK7),sK7)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f384,plain,
    ( spl9_60
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f352,f197,f143,f382])).

fof(f382,plain,
    ( spl9_60
  <=> v1_funct_1(u1_waybel_0(sK8,sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f197,plain,
    ( spl9_18
  <=> l1_waybel_0(sK4(sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f352,plain,
    ( v1_funct_1(u1_waybel_0(sK8,sK4(sK8)))
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f144,f198,f110])).

fof(f198,plain,
    ( l1_waybel_0(sK4(sK8),sK8)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f377,plain,
    ( spl9_58
    | ~ spl9_0
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f349,f183,f129,f375])).

fof(f375,plain,
    ( spl9_58
  <=> v1_funct_1(u1_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f183,plain,
    ( spl9_14
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f349,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK4(sK0)))
    | ~ spl9_0
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f130,f184,f110])).

fof(f184,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f369,plain,
    ( spl9_56
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f348,f150,f129,f367])).

fof(f367,plain,
    ( spl9_56
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f348,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f130,f151,f110])).

fof(f361,plain,
    ( spl9_54
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f354,f345,f359])).

fof(f359,plain,
    ( spl9_54
  <=> l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f345,plain,
    ( spl9_52
  <=> l1_orders_2(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f354,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f346,f93])).

fof(f346,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f347,plain,
    ( spl9_52
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f340,f337,f249,f345])).

fof(f340,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(unit_resulting_resolution,[],[f250,f338,f99])).

fof(f339,plain,
    ( spl9_50
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f252,f249,f337])).

fof(f252,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f250,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',existence_l1_waybel_0)).

fof(f331,plain,
    ( spl9_48
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f323,f319,f329])).

fof(f329,plain,
    ( spl9_48
  <=> l1_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f319,plain,
    ( spl9_46
  <=> l1_orders_2(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f323,plain,
    ( l1_struct_0(sK3(sK1))
    | ~ spl9_46 ),
    inference(unit_resulting_resolution,[],[f320,f93])).

fof(f320,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( spl9_46
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f314,f311,f240,f319])).

fof(f311,plain,
    ( spl9_44
  <=> m1_yellow_0(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f314,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f241,f312,f98])).

fof(f312,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f311])).

fof(f313,plain,
    ( spl9_44
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f243,f240,f311])).

fof(f243,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f241,f103])).

fof(f305,plain,
    ( spl9_42
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f297,f286,f303])).

fof(f303,plain,
    ( spl9_42
  <=> l1_struct_0(sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f286,plain,
    ( spl9_38
  <=> l1_orders_2(sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f297,plain,
    ( l1_struct_0(sK4(sK7))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f287,f93])).

fof(f287,plain,
    ( l1_orders_2(sK4(sK7))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f286])).

fof(f295,plain,
    ( spl9_40
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f273,f269,f293])).

fof(f293,plain,
    ( spl9_40
  <=> l1_struct_0(sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f269,plain,
    ( spl9_34
  <=> l1_orders_2(sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f273,plain,
    ( l1_struct_0(sK4(sK8))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f270,f93])).

fof(f270,plain,
    ( l1_orders_2(sK4(sK8))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f288,plain,
    ( spl9_38
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f235,f204,f165,f286])).

fof(f235,plain,
    ( l1_orders_2(sK4(sK7))
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f166,f205,f99])).

fof(f280,plain,
    ( spl9_36
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f264,f257,f278])).

fof(f278,plain,
    ( spl9_36
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f264,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f258,f93])).

fof(f271,plain,
    ( spl9_34
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f234,f197,f143,f269])).

fof(f234,plain,
    ( l1_orders_2(sK4(sK8))
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f144,f198,f99])).

fof(f259,plain,
    ( spl9_32
    | ~ spl9_0
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f233,f183,f129,f257])).

fof(f233,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl9_0
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f130,f184,f99])).

fof(f251,plain,
    ( spl9_30
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f244,f240,f249])).

fof(f244,plain,
    ( l1_struct_0(sK1)
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f241,f93])).

fof(f242,plain,
    ( spl9_28
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f232,f150,f129,f240])).

fof(f232,plain,
    ( l1_orders_2(sK1)
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f130,f151,f99])).

fof(f231,plain,
    ( spl9_26
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f215,f212,f229])).

fof(f229,plain,
    ( spl9_26
  <=> m1_yellow_0(sK3(sK3(sK7)),sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f212,plain,
    ( spl9_22
  <=> l1_orders_2(sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f215,plain,
    ( m1_yellow_0(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f213,f103])).

fof(f213,plain,
    ( l1_orders_2(sK3(sK7))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f223,plain,
    ( spl9_24
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f216,f212,f221])).

fof(f221,plain,
    ( spl9_24
  <=> l1_struct_0(sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f216,plain,
    ( l1_struct_0(sK3(sK7))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f213,f93])).

fof(f214,plain,
    ( spl9_22
    | ~ spl9_2
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f207,f190,f136,f212])).

fof(f190,plain,
    ( spl9_16
  <=> m1_yellow_0(sK3(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f207,plain,
    ( l1_orders_2(sK3(sK7))
    | ~ spl9_2
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f191,f98])).

fof(f191,plain,
    ( m1_yellow_0(sK3(sK7),sK7)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f206,plain,
    ( spl9_20
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f178,f165,f204])).

fof(f178,plain,
    ( l1_waybel_0(sK4(sK7),sK7)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f166,f104])).

fof(f199,plain,
    ( spl9_18
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f177,f143,f197])).

fof(f177,plain,
    ( l1_waybel_0(sK4(sK8),sK8)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f144,f104])).

fof(f192,plain,
    ( spl9_16
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f175,f136,f190])).

fof(f175,plain,
    ( m1_yellow_0(sK3(sK7),sK7)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f137,f103])).

fof(f185,plain,
    ( spl9_14
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f176,f129,f183])).

fof(f176,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl9_0 ),
    inference(unit_resulting_resolution,[],[f130,f104])).

fof(f174,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f91,f172])).

fof(f91,plain,(
    ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f69,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
     => ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK1))
            & m1_yellow_6(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
          & m1_yellow_6(X2,X0,X1) )
     => ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
        & m1_yellow_6(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',t19_yellow_6)).

fof(f167,plain,
    ( spl9_10
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f160,f136,f165])).

fof(f160,plain,
    ( l1_struct_0(sK7)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f137,f93])).

fof(f159,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f90,f157])).

fof(f90,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f152,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f89,f150])).

fof(f89,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f145,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f124,f143])).

fof(f124,plain,(
    l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    l1_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f86])).

fof(f86,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',existence_l1_struct_0)).

fof(f138,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f123,f136])).

fof(f123,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    l1_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f84])).

fof(f84,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK7) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t19_yellow_6.p',existence_l1_orders_2)).

fof(f131,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f88,f129])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
