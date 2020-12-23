%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t16_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 609 expanded)
%              Number of leaves         :   52 ( 271 expanded)
%              Depth                    :   11
%              Number of atoms          :  587 (1733 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f111,f118,f125,f134,f141,f151,f160,f169,f177,f185,f193,f201,f209,f218,f227,f235,f243,f252,f260,f268,f276,f291,f299,f320,f328,f339,f347,f356,f376,f386,f397,f417,f427,f441,f451,f458,f465,f475,f494,f496,f498,f500,f502,f504,f509])).

fof(f509,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f507,f96])).

fof(f96,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f507,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f506,f159])).

fof(f159,plain,
    ( l1_orders_2(sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_16
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f506,plain,
    ( ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f505,f396])).

fof(f396,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl6_64
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f505,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f493,f440])).

fof(f440,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl6_70
  <=> r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f493,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f73,f124])).

fof(f124,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_9
  <=> ~ m1_yellow_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',d13_yellow_0)).

fof(f504,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f484,f440])).

fof(f484,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f96,f159,f124,f396,f73])).

fof(f502,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f487,f396])).

fof(f487,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f96,f159,f124,f440,f73])).

fof(f500,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f488,f124])).

fof(f488,plain,
    ( m1_yellow_0(sK2,sK0)
    | ~ spl6_0
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f96,f159,f396,f440,f73])).

fof(f498,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f489,f159])).

fof(f489,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f96,f124,f396,f440,f73])).

fof(f496,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f490,f96])).

fof(f490,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f159,f124,f396,f440,f73])).

fof(f494,plain,
    ( ~ spl6_0
    | spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_64
    | ~ spl6_70 ),
    inference(unit_resulting_resolution,[],[f96,f159,f124,f396,f440,f73])).

fof(f475,plain,
    ( spl6_78
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f420,f415,f473])).

fof(f473,plain,
    ( spl6_78
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f415,plain,
    ( spl6_66
  <=> r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f420,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0)))
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f416,f81])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',t3_subset)).

fof(f416,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f415])).

fof(f465,plain,
    ( spl6_76
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f400,f167,f132,f95,f463])).

fof(f463,plain,
    ( spl6_76
  <=> r1_tarski(u1_orders_2(sK3(sK0)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f132,plain,
    ( spl6_10
  <=> m1_yellow_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f167,plain,
    ( spl6_18
  <=> l1_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f400,plain,
    ( r1_tarski(u1_orders_2(sK3(sK0)),u1_orders_2(sK0))
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f96,f168,f133,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f133,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f168,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f458,plain,
    ( spl6_74
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f379,f374,f456])).

fof(f456,plain,
    ( spl6_74
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f374,plain,
    ( spl6_60
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f379,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_60 ),
    inference(unit_resulting_resolution,[],[f375,f81])).

fof(f375,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f374])).

fof(f451,plain,
    ( spl6_72
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f359,f167,f132,f95,f449])).

fof(f449,plain,
    ( spl6_72
  <=> r1_tarski(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f359,plain,
    ( r1_tarski(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f96,f168,f133,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f441,plain,
    ( spl6_70
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f428,f425,f415,f439])).

fof(f425,plain,
    ( spl6_68
  <=> r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f428,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f416,f426,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',t1_xboole_1)).

fof(f426,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f425])).

fof(f427,plain,
    ( spl6_68
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f399,f158,f149,f116,f425])).

fof(f116,plain,
    ( spl6_6
  <=> m1_yellow_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f149,plain,
    ( spl6_14
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f399,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f150,f159,f117,f72])).

fof(f117,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f150,plain,
    ( l1_orders_2(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f417,plain,
    ( spl6_66
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f398,f149,f109,f95,f415])).

fof(f109,plain,
    ( spl6_4
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f398,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f96,f150,f110,f72])).

fof(f110,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f397,plain,
    ( spl6_64
    | ~ spl6_60
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f387,f384,f374,f395])).

fof(f384,plain,
    ( spl6_62
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f387,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl6_60
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f375,f385,f84])).

fof(f385,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f384])).

fof(f386,plain,
    ( spl6_62
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f358,f158,f149,f116,f384])).

fof(f358,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f150,f159,f117,f71])).

fof(f376,plain,
    ( spl6_60
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f357,f149,f109,f95,f374])).

fof(f357,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f96,f150,f110,f71])).

fof(f356,plain,
    ( spl6_58
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f277,f274,f354])).

fof(f354,plain,
    ( spl6_58
  <=> m1_yellow_0(sK3(sK3(sK3(sK2))),sK3(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f274,plain,
    ( spl6_44
  <=> l1_orders_2(sK3(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f277,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK2))),sK3(sK3(sK2)))
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f275,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
     => m1_yellow_0(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_yellow_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',existence_m1_yellow_0)).

fof(f275,plain,
    ( l1_orders_2(sK3(sK3(sK2)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f274])).

fof(f347,plain,
    ( spl6_56
    | ~ spl6_40
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f340,f337,f258,f345])).

fof(f345,plain,
    ( spl6_56
  <=> l1_orders_2(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f258,plain,
    ( spl6_40
  <=> l1_orders_2(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f337,plain,
    ( spl6_54
  <=> m1_yellow_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f340,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK1))))
    | ~ spl6_40
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f259,f338,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',dt_m1_yellow_0)).

fof(f338,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f337])).

fof(f259,plain,
    ( l1_orders_2(sK3(sK3(sK1)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f258])).

fof(f339,plain,
    ( spl6_54
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f261,f258,f337])).

fof(f261,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f259,f75])).

fof(f328,plain,
    ( spl6_52
    | ~ spl6_36
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f321,f318,f241,f326])).

fof(f326,plain,
    ( spl6_52
  <=> l1_orders_2(sK3(sK3(sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f241,plain,
    ( spl6_36
  <=> l1_orders_2(sK3(sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f318,plain,
    ( spl6_50
  <=> m1_yellow_0(sK3(sK3(sK3(sK5))),sK3(sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f321,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK5))))
    | ~ spl6_36
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f242,f319,f74])).

fof(f319,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK5))),sK3(sK3(sK5)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f318])).

fof(f242,plain,
    ( l1_orders_2(sK3(sK3(sK5)))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f241])).

fof(f320,plain,
    ( spl6_50
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f245,f241,f318])).

fof(f245,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK5))),sK3(sK3(sK5)))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f242,f75])).

fof(f299,plain,
    ( spl6_48
    | ~ spl6_32
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f292,f289,f225,f297])).

fof(f297,plain,
    ( spl6_48
  <=> l1_orders_2(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f225,plain,
    ( spl6_32
  <=> l1_orders_2(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f289,plain,
    ( spl6_46
  <=> m1_yellow_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f292,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK0))))
    | ~ spl6_32
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f226,f290,f74])).

fof(f290,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f289])).

fof(f226,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f225])).

fof(f291,plain,
    ( spl6_46
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f228,f225,f289])).

fof(f228,plain,
    ( m1_yellow_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f226,f75])).

fof(f276,plain,
    ( spl6_44
    | ~ spl6_28
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f269,f266,f207,f274])).

fof(f207,plain,
    ( spl6_28
  <=> l1_orders_2(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f266,plain,
    ( spl6_42
  <=> m1_yellow_0(sK3(sK3(sK2)),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f269,plain,
    ( l1_orders_2(sK3(sK3(sK2)))
    | ~ spl6_28
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f208,f267,f74])).

fof(f267,plain,
    ( m1_yellow_0(sK3(sK3(sK2)),sK3(sK2))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f266])).

fof(f208,plain,
    ( l1_orders_2(sK3(sK2))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f207])).

fof(f268,plain,
    ( spl6_42
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f210,f207,f266])).

fof(f210,plain,
    ( m1_yellow_0(sK3(sK3(sK2)),sK3(sK2))
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f208,f75])).

fof(f260,plain,
    ( spl6_40
    | ~ spl6_24
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f253,f250,f191,f258])).

fof(f191,plain,
    ( spl6_24
  <=> l1_orders_2(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f250,plain,
    ( spl6_38
  <=> m1_yellow_0(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f253,plain,
    ( l1_orders_2(sK3(sK3(sK1)))
    | ~ spl6_24
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f192,f251,f74])).

fof(f251,plain,
    ( m1_yellow_0(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f250])).

fof(f192,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f191])).

fof(f252,plain,
    ( spl6_38
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f194,f191,f250])).

fof(f194,plain,
    ( m1_yellow_0(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f192,f75])).

fof(f243,plain,
    ( spl6_36
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f236,f233,f175,f241])).

fof(f175,plain,
    ( spl6_20
  <=> l1_orders_2(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f233,plain,
    ( spl6_34
  <=> m1_yellow_0(sK3(sK3(sK5)),sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f236,plain,
    ( l1_orders_2(sK3(sK3(sK5)))
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f176,f234,f74])).

fof(f234,plain,
    ( m1_yellow_0(sK3(sK3(sK5)),sK3(sK5))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f233])).

fof(f176,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f235,plain,
    ( spl6_34
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f178,f175,f233])).

fof(f178,plain,
    ( m1_yellow_0(sK3(sK3(sK5)),sK3(sK5))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f176,f75])).

fof(f227,plain,
    ( spl6_32
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f219,f216,f167,f225])).

fof(f216,plain,
    ( spl6_30
  <=> m1_yellow_0(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f219,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f168,f217,f74])).

fof(f217,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f216])).

fof(f218,plain,
    ( spl6_30
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f170,f167,f216])).

fof(f170,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f168,f75])).

fof(f209,plain,
    ( spl6_28
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f202,f199,f158,f207])).

fof(f199,plain,
    ( spl6_26
  <=> m1_yellow_0(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f202,plain,
    ( l1_orders_2(sK3(sK2))
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f159,f200,f74])).

fof(f200,plain,
    ( m1_yellow_0(sK3(sK2),sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( spl6_26
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f161,f158,f199])).

fof(f161,plain,
    ( m1_yellow_0(sK3(sK2),sK2)
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f159,f75])).

fof(f193,plain,
    ( spl6_24
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f186,f183,f149,f191])).

fof(f183,plain,
    ( spl6_22
  <=> m1_yellow_0(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f186,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f150,f184,f74])).

fof(f184,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl6_22
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f153,f149,f183])).

fof(f153,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f150,f75])).

fof(f177,plain,
    ( spl6_20
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f144,f139,f102,f175])).

fof(f102,plain,
    ( spl6_2
  <=> l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f139,plain,
    ( spl6_12
  <=> m1_yellow_0(sK3(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f144,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f103,f140,f74])).

fof(f140,plain,
    ( m1_yellow_0(sK3(sK5),sK5)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f103,plain,
    ( l1_orders_2(sK5)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f169,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f143,f132,f95,f167])).

fof(f143,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f96,f133,f74])).

fof(f160,plain,
    ( spl6_16
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f152,f149,f116,f158])).

fof(f152,plain,
    ( l1_orders_2(sK2)
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f117,f150,f74])).

fof(f151,plain,
    ( spl6_14
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f142,f109,f95,f149])).

fof(f142,plain,
    ( l1_orders_2(sK1)
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f96,f110,f74])).

fof(f141,plain,
    ( spl6_12
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f127,f102,f139])).

fof(f127,plain,
    ( m1_yellow_0(sK3(sK5),sK5)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f103,f75])).

fof(f134,plain,
    ( spl6_10
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f126,f95,f132])).

fof(f126,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f96,f75])).

fof(f125,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f68,f123])).

fof(f68,plain,(
    ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    & m1_yellow_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow_0(X2,X0)
                & m1_yellow_0(X2,X1) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,sK0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_yellow_0(X2,X0)
            & m1_yellow_0(X2,sK1) )
        & m1_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_yellow_0(X2,X0)
          & m1_yellow_0(X2,X1) )
     => ( ~ m1_yellow_0(sK2,X0)
        & m1_yellow_0(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_0(X2,X1)
               => m1_yellow_0(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',t16_yellow_6)).

fof(f118,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f67,f116])).

fof(f67,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f66,f109])).

fof(f66,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f90,f102])).

fof(f90,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f63])).

fof(f63,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK5) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t16_yellow_6.p',existence_l1_orders_2)).

fof(f97,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f65,f95])).

fof(f65,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
