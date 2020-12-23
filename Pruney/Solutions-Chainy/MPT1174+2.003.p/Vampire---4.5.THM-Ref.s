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
% DateTime   : Thu Dec  3 13:10:14 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 442 expanded)
%              Number of leaves         :   40 ( 211 expanded)
%              Depth                    :   16
%              Number of atoms          :  906 (2178 expanded)
%              Number of equality atoms :   52 ( 298 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f151,f161,f202,f215,f224,f229,f331,f416,f488,f548,f584,f587])).

fof(f587,plain,
    ( ~ spl9_39
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_12
    | ~ spl9_16
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f513,f297,f221,f156,f125,f120,f115,f110,f382])).

fof(f382,plain,
    ( spl9_39
  <=> r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f110,plain,
    ( spl9_5
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f115,plain,
    ( spl9_6
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f120,plain,
    ( spl9_7
  <=> v5_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f125,plain,
    ( spl9_8
  <=> v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f156,plain,
    ( spl9_12
  <=> r2_orders_2(sK4,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f221,plain,
    ( spl9_16
  <=> m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f297,plain,
    ( spl9_27
  <=> r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f513,plain,
    ( ~ r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_12
    | ~ spl9_16
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f127,f122,f117,f112,f158,f112,f223,f299,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X3)
      | r2_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(f299,plain,
    ( r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f223,plain,
    ( m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f158,plain,
    ( ~ r2_orders_2(sK4,sK5,sK5)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f112,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( l1_orders_2(sK4)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( v5_orders_2(sK4)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f120])).

% (5858)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f127,plain,
    ( v4_orders_2(sK4)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f584,plain,
    ( ~ spl9_17
    | ~ spl9_31
    | spl9_52 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | ~ spl9_17
    | ~ spl9_31
    | spl9_52 ),
    inference(subsumption_resolution,[],[f580,f228])).

fof(f228,plain,
    ( r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl9_17
  <=> r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f580,plain,
    ( ~ r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5))
    | ~ spl9_31
    | spl9_52 ),
    inference(unit_resulting_resolution,[],[f330,f554,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k3_orders_2(X0,X3,X1))
      | sP2(X3,X2,X1,X0)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X2,k3_orders_2(X0,X3,X1))
          | ~ sP2(X3,X2,X1,X0) )
        & ( sP2(X3,X2,X1,X0)
          | ~ r2_hidden(X2,k3_orders_2(X0,X3,X1)) ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1,X3] :
      ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
          | ~ sP2(X3,X1,X2,X0) )
        & ( sP2(X3,X1,X2,X0)
          | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
      | ~ sP3(X0,X2,X1,X3) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1,X3] :
      ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      <=> sP2(X3,X1,X2,X0) )
      | ~ sP3(X0,X2,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f554,plain,
    ( ! [X0,X1] : ~ sP2(sK7,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),X0,X1)
    | spl9_52 ),
    inference(unit_resulting_resolution,[],[f547,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ~ r2_hidden(X1,X0)
        | ~ r2_orders_2(X3,X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_orders_2(X3,X1,X2) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP2(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP2(X3,X1,X2,X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP2(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP2(X3,X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X3,X1,X2,X0] :
      ( sP2(X3,X1,X2,X0)
    <=> ( r2_hidden(X1,X3)
        & r2_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f547,plain,
    ( ~ r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)
    | spl9_52 ),
    inference(avatar_component_clause,[],[f545])).

fof(f545,plain,
    ( spl9_52
  <=> r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f330,plain,
    ( sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl9_31
  <=> sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f548,plain,
    ( ~ spl9_52
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | spl9_42 ),
    inference(avatar_split_clause,[],[f541,f413,f135,f130,f125,f120,f115,f110,f105,f100,f95,f545])).

fof(f95,plain,
    ( spl9_2
  <=> sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f100,plain,
    ( spl9_3
  <=> m2_orders_2(sK7,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f105,plain,
    ( spl9_4
  <=> m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f130,plain,
    ( spl9_9
  <=> v3_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f135,plain,
    ( spl9_10
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f413,plain,
    ( spl9_42
  <=> r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f541,plain,
    ( ~ r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | spl9_42 ),
    inference(unit_resulting_resolution,[],[f102,f415,f512])).

fof(f512,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(subsumption_resolution,[],[f511,f236])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X1,u1_struct_0(sK4))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(resolution,[],[f207,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f207,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m2_orders_2(X0,sK4,sK6) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(subsumption_resolution,[],[f206,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK4)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | v2_struct_0(sK4) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f205,f132])).

% (5865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f132,plain,
    ( v3_orders_2(sK4)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f204,f127])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f203,f122])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f197,f117])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK4,sK6)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_4 ),
    inference(resolution,[],[f82,f107])).

fof(f107,plain,
    ( m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f511,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(subsumption_resolution,[],[f510,f137])).

fof(f510,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f509,f132])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f508,f127])).

fof(f508,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f507,f122])).

fof(f507,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f506,f117])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f505,f112])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f503,f107])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK4,sK6)
        | ~ m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl9_2 ),
    inference(superposition,[],[f88,f97])).

fof(f97,plain,
    ( sK5 = k1_funct_1(sK6,u1_struct_0(sK4))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f88,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

fof(f415,plain,
    ( ~ r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))
    | spl9_42 ),
    inference(avatar_component_clause,[],[f413])).

fof(f102,plain,
    ( m2_orders_2(sK7,sK4,sK6)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f488,plain,
    ( ~ spl9_17
    | spl9_27
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl9_17
    | spl9_27
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f485,f228])).

fof(f485,plain,
    ( ~ r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5))
    | spl9_27
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f330,f397,f71])).

fof(f397,plain,
    ( ! [X0] : ~ sP2(X0,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5,sK4)
    | spl9_27 ),
    inference(unit_resulting_resolution,[],[f298,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | r2_orders_2(X3,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f298,plain,
    ( ~ r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5)
    | spl9_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f416,plain,
    ( ~ spl9_42
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | spl9_10
    | ~ spl9_16
    | spl9_39 ),
    inference(avatar_split_clause,[],[f408,f382,f221,f135,f130,f115,f110,f413])).

fof(f408,plain,
    ( ~ r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | spl9_10
    | ~ spl9_16
    | spl9_39 ),
    inference(unit_resulting_resolution,[],[f137,f132,f117,f112,f223,f384,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f384,plain,
    ( ~ r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))
    | spl9_39 ),
    inference(avatar_component_clause,[],[f382])).

fof(f331,plain,
    ( spl9_31
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f314,f221,f199,f135,f130,f125,f120,f115,f110,f328])).

fof(f199,plain,
    ( spl9_14
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f314,plain,
    ( sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f223,f112,f201,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X2,X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP3(X0,X2,X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f35,f34])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f201,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f229,plain,
    ( spl9_17
    | spl9_1
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f217,f212,f90,f226])).

fof(f90,plain,
    ( spl9_1
  <=> k1_xboole_0 = k3_orders_2(sK4,sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f212,plain,
    ( spl9_15
  <=> m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f217,plain,
    ( r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5))
    | spl9_1
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f92,f214,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f214,plain,
    ( m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f212])).

fof(f92,plain,
    ( k1_xboole_0 != k3_orders_2(sK4,sK7,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f224,plain,
    ( spl9_16
    | spl9_1
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f218,f212,f90,f221])).

fof(f218,plain,
    ( m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4))
    | spl9_1
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f92,f214,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f215,plain,
    ( spl9_15
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f209,f199,f135,f130,f125,f120,f115,f110,f212])).

fof(f209,plain,
    ( m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f112,f201,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f202,plain,
    ( spl9_14
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(avatar_split_clause,[],[f196,f135,f130,f125,f120,f115,f105,f100,f199])).

fof(f196,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_10 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f102,f107,f82])).

fof(f161,plain,
    ( ~ spl9_12
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f160,f148,f156])).

fof(f148,plain,
    ( spl9_11
  <=> sP1(sK4,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f160,plain,
    ( ~ r2_orders_2(sK4,sK5,sK5)
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f154,f87])).

fof(f87,plain,(
    ! [X2,X1] : ~ sP0(X1,X1,X2) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f154,plain,
    ( ~ r2_orders_2(sK4,sK5,sK5)
    | sP0(sK5,sK5,sK4)
    | ~ spl9_11 ),
    inference(resolution,[],[f150,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f150,plain,
    ( sP1(sK4,sK5,sK5)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( spl9_11
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f144,f115,f110,f148])).

fof(f144,plain,
    ( sP1(sK4,sK5,sK5)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f117,f112,f112,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f14,f32,f31])).

% (5854)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f138,plain,(
    ~ spl9_10 ),
    inference(avatar_split_clause,[],[f54,f135])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != k3_orders_2(sK4,sK7,sK5)
    & sK5 = k1_funct_1(sK6,u1_struct_0(sK4))
    & m2_orders_2(sK7,sK4,sK6)
    & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK4,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK4)) = X1
                  & m2_orders_2(X3,sK4,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(sK4,X3,X1)
                & k1_funct_1(X2,u1_struct_0(sK4)) = X1
                & m2_orders_2(X3,sK4,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4))) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(sK4,X3,sK5)
              & k1_funct_1(X2,u1_struct_0(sK4)) = sK5
              & m2_orders_2(X3,sK4,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(sK4,X3,sK5)
            & k1_funct_1(X2,u1_struct_0(sK4)) = sK5
            & m2_orders_2(X3,sK4,X2) )
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4))) )
   => ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(sK4,X3,sK5)
          & sK5 = k1_funct_1(sK6,u1_struct_0(sK4))
          & m2_orders_2(X3,sK4,sK6) )
      & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( k1_xboole_0 != k3_orders_2(sK4,X3,sK5)
        & sK5 = k1_funct_1(sK6,u1_struct_0(sK4))
        & m2_orders_2(X3,sK4,sK6) )
   => ( k1_xboole_0 != k3_orders_2(sK4,sK7,sK5)
      & sK5 = k1_funct_1(sK6,u1_struct_0(sK4))
      & m2_orders_2(sK7,sK4,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

fof(f133,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f55,f130])).

fof(f55,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f128,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f56,f125])).

fof(f56,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f123,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f57,f120])).

fof(f57,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f118,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f59,f110])).

fof(f59,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f60,f105])).

fof(f60,plain,(
    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f61,f100])).

fof(f61,plain,(
    m2_orders_2(sK7,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f62,f95])).

fof(f62,plain,(
    sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f63,f90])).

fof(f63,plain,(
    k1_xboole_0 != k3_orders_2(sK4,sK7,sK5) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:20:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (5847)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (5848)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (5845)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (5846)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5855)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (5845)Refutation not found, incomplete strategy% (5845)------------------------------
% 0.20/0.52  % (5845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5845)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5845)Memory used [KB]: 6140
% 0.20/0.52  % (5845)Time elapsed: 0.068 s
% 0.20/0.52  % (5845)------------------------------
% 0.20/0.52  % (5845)------------------------------
% 0.20/0.52  % (5859)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (5850)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.21/0.53  % (5860)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.21/0.53  % (5861)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.21/0.54  % (5846)Refutation not found, incomplete strategy% (5846)------------------------------
% 1.21/0.54  % (5846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (5846)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (5846)Memory used [KB]: 10618
% 1.21/0.54  % (5846)Time elapsed: 0.101 s
% 1.21/0.54  % (5846)------------------------------
% 1.21/0.54  % (5846)------------------------------
% 1.21/0.54  % (5861)Refutation found. Thanks to Tanya!
% 1.21/0.54  % SZS status Theorem for theBenchmark
% 1.21/0.54  % SZS output start Proof for theBenchmark
% 1.21/0.54  fof(f588,plain,(
% 1.21/0.54    $false),
% 1.21/0.54    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f151,f161,f202,f215,f224,f229,f331,f416,f488,f548,f584,f587])).
% 1.21/0.54  fof(f587,plain,(
% 1.21/0.54    ~spl9_39 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | spl9_12 | ~spl9_16 | ~spl9_27),
% 1.21/0.54    inference(avatar_split_clause,[],[f513,f297,f221,f156,f125,f120,f115,f110,f382])).
% 1.21/0.54  fof(f382,plain,(
% 1.21/0.54    spl9_39 <=> r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 1.21/0.54  fof(f110,plain,(
% 1.21/0.54    spl9_5 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.21/0.54  fof(f115,plain,(
% 1.21/0.54    spl9_6 <=> l1_orders_2(sK4)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.21/0.54  fof(f120,plain,(
% 1.21/0.54    spl9_7 <=> v5_orders_2(sK4)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.21/0.54  fof(f125,plain,(
% 1.21/0.54    spl9_8 <=> v4_orders_2(sK4)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.21/0.54  fof(f156,plain,(
% 1.21/0.54    spl9_12 <=> r2_orders_2(sK4,sK5,sK5)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.21/0.54  fof(f221,plain,(
% 1.21/0.54    spl9_16 <=> m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.21/0.54  fof(f297,plain,(
% 1.21/0.54    spl9_27 <=> r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.21/0.54  fof(f513,plain,(
% 1.21/0.54    ~r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | spl9_12 | ~spl9_16 | ~spl9_27)),
% 1.21/0.54    inference(unit_resulting_resolution,[],[f127,f122,f117,f112,f158,f112,f223,f299,f78])).
% 1.21/0.54  fof(f78,plain,(
% 1.21/0.54    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X3) | r2_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f20])).
% 1.21/0.54  fof(f20,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 1.21/0.54    inference(flattening,[],[f19])).
% 1.21/0.54  fof(f19,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 1.21/0.54    inference(ennf_transformation,[],[f7])).
% 1.21/0.54  fof(f7,axiom,(
% 1.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 1.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).
% 1.21/0.54  fof(f299,plain,(
% 1.21/0.54    r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5) | ~spl9_27),
% 1.21/0.54    inference(avatar_component_clause,[],[f297])).
% 1.21/0.54  fof(f223,plain,(
% 1.21/0.54    m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4)) | ~spl9_16),
% 1.21/0.54    inference(avatar_component_clause,[],[f221])).
% 1.21/0.54  fof(f158,plain,(
% 1.21/0.54    ~r2_orders_2(sK4,sK5,sK5) | spl9_12),
% 1.21/0.54    inference(avatar_component_clause,[],[f156])).
% 1.21/0.54  fof(f112,plain,(
% 1.21/0.54    m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl9_5),
% 1.21/0.54    inference(avatar_component_clause,[],[f110])).
% 1.21/0.54  fof(f117,plain,(
% 1.21/0.54    l1_orders_2(sK4) | ~spl9_6),
% 1.21/0.54    inference(avatar_component_clause,[],[f115])).
% 1.21/0.54  fof(f122,plain,(
% 1.21/0.54    v5_orders_2(sK4) | ~spl9_7),
% 1.21/0.54    inference(avatar_component_clause,[],[f120])).
% 1.21/0.54  % (5858)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.21/0.54  fof(f127,plain,(
% 1.21/0.54    v4_orders_2(sK4) | ~spl9_8),
% 1.21/0.54    inference(avatar_component_clause,[],[f125])).
% 1.21/0.54  fof(f584,plain,(
% 1.21/0.54    ~spl9_17 | ~spl9_31 | spl9_52),
% 1.21/0.54    inference(avatar_contradiction_clause,[],[f583])).
% 1.21/0.54  fof(f583,plain,(
% 1.21/0.54    $false | (~spl9_17 | ~spl9_31 | spl9_52)),
% 1.21/0.54    inference(subsumption_resolution,[],[f580,f228])).
% 1.21/0.54  fof(f228,plain,(
% 1.21/0.54    r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5)) | ~spl9_17),
% 1.21/0.54    inference(avatar_component_clause,[],[f226])).
% 1.21/0.54  fof(f226,plain,(
% 1.21/0.54    spl9_17 <=> r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.21/0.54  fof(f580,plain,(
% 1.21/0.54    ~r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5)) | (~spl9_31 | spl9_52)),
% 1.21/0.54    inference(unit_resulting_resolution,[],[f330,f554,f71])).
% 1.21/0.54  fof(f71,plain,(
% 1.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k3_orders_2(X0,X3,X1)) | sP2(X3,X2,X1,X0) | ~sP3(X0,X1,X2,X3)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f47])).
% 1.21/0.54  fof(f47,plain,(
% 1.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(X2,k3_orders_2(X0,X3,X1)) | ~sP2(X3,X2,X1,X0)) & (sP2(X3,X2,X1,X0) | ~r2_hidden(X2,k3_orders_2(X0,X3,X1)))) | ~sP3(X0,X1,X2,X3))),
% 1.21/0.54    inference(rectify,[],[f46])).
% 1.21/0.54  fof(f46,plain,(
% 1.21/0.54    ! [X0,X2,X1,X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~sP2(X3,X1,X2,X0)) & (sP2(X3,X1,X2,X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~sP3(X0,X2,X1,X3))),
% 1.21/0.54    inference(nnf_transformation,[],[f35])).
% 1.21/0.54  fof(f35,plain,(
% 1.21/0.54    ! [X0,X2,X1,X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> sP2(X3,X1,X2,X0)) | ~sP3(X0,X2,X1,X3))),
% 1.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.21/0.54  fof(f554,plain,(
% 1.21/0.54    ( ! [X0,X1] : (~sP2(sK7,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),X0,X1)) ) | spl9_52),
% 1.21/0.54    inference(unit_resulting_resolution,[],[f547,f74])).
% 1.21/0.54  fof(f74,plain,(
% 1.21/0.54    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | r2_hidden(X1,X0)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f50])).
% 1.21/0.54  fof(f50,plain,(
% 1.21/0.54    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ~r2_hidden(X1,X0) | ~r2_orders_2(X3,X1,X2)) & ((r2_hidden(X1,X0) & r2_orders_2(X3,X1,X2)) | ~sP2(X0,X1,X2,X3)))),
% 1.21/0.54    inference(rectify,[],[f49])).
% 1.21/0.54  fof(f49,plain,(
% 1.21/0.54    ! [X3,X1,X2,X0] : ((sP2(X3,X1,X2,X0) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP2(X3,X1,X2,X0)))),
% 1.21/0.54    inference(flattening,[],[f48])).
% 1.21/0.54  fof(f48,plain,(
% 1.21/0.54    ! [X3,X1,X2,X0] : ((sP2(X3,X1,X2,X0) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP2(X3,X1,X2,X0)))),
% 1.21/0.54    inference(nnf_transformation,[],[f34])).
% 1.21/0.54  fof(f34,plain,(
% 1.21/0.54    ! [X3,X1,X2,X0] : (sP2(X3,X1,X2,X0) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))),
% 1.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.21/0.54  fof(f547,plain,(
% 1.21/0.54    ~r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) | spl9_52),
% 1.21/0.54    inference(avatar_component_clause,[],[f545])).
% 1.21/0.54  fof(f545,plain,(
% 1.21/0.54    spl9_52 <=> r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 1.21/0.54  fof(f330,plain,(
% 1.21/0.54    sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) | ~spl9_31),
% 1.21/0.54    inference(avatar_component_clause,[],[f328])).
% 1.21/0.54  fof(f328,plain,(
% 1.21/0.54    spl9_31 <=> sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.21/0.54  fof(f548,plain,(
% 1.21/0.54    ~spl9_52 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | spl9_42),
% 1.21/0.54    inference(avatar_split_clause,[],[f541,f413,f135,f130,f125,f120,f115,f110,f105,f100,f95,f545])).
% 1.21/0.54  fof(f95,plain,(
% 1.21/0.54    spl9_2 <=> sK5 = k1_funct_1(sK6,u1_struct_0(sK4))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.21/0.54  fof(f100,plain,(
% 1.21/0.54    spl9_3 <=> m2_orders_2(sK7,sK4,sK6)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.21/0.54  fof(f105,plain,(
% 1.21/0.54    spl9_4 <=> m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.21/0.54  fof(f130,plain,(
% 1.21/0.54    spl9_9 <=> v3_orders_2(sK4)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.21/0.54  fof(f135,plain,(
% 1.21/0.54    spl9_10 <=> v2_struct_0(sK4)),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.21/0.54  fof(f413,plain,(
% 1.21/0.54    spl9_42 <=> r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)))),
% 1.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.21/0.54  fof(f541,plain,(
% 1.21/0.54    ~r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | spl9_42)),
% 1.21/0.54    inference(unit_resulting_resolution,[],[f102,f415,f512])).
% 1.21/0.54  fof(f512,plain,(
% 1.21/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10)),
% 1.21/0.54    inference(subsumption_resolution,[],[f511,f236])).
% 1.21/0.54  fof(f236,plain,(
% 1.21/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X1,u1_struct_0(sK4)) | ~r2_hidden(X1,X0)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10)),
% 1.21/0.54    inference(resolution,[],[f207,f86])).
% 1.21/0.54  fof(f86,plain,(
% 1.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f30])).
% 1.21/0.54  fof(f30,plain,(
% 1.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.21/0.54    inference(flattening,[],[f29])).
% 1.21/0.54  fof(f29,plain,(
% 1.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.21/0.54    inference(ennf_transformation,[],[f2])).
% 1.21/0.54  fof(f2,axiom,(
% 1.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.21/0.54  fof(f207,plain,(
% 1.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m2_orders_2(X0,sK4,sK6)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10)),
% 1.21/0.54    inference(subsumption_resolution,[],[f206,f137])).
% 1.21/0.54  fof(f137,plain,(
% 1.21/0.54    ~v2_struct_0(sK4) | spl9_10),
% 1.21/0.54    inference(avatar_component_clause,[],[f135])).
% 1.21/0.54  fof(f206,plain,(
% 1.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9)),
% 1.21/0.54    inference(subsumption_resolution,[],[f205,f132])).
% 1.21/0.54  % (5865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.45/0.54  fof(f132,plain,(
% 1.45/0.54    v3_orders_2(sK4) | ~spl9_9),
% 1.45/0.54    inference(avatar_component_clause,[],[f130])).
% 1.45/0.54  fof(f205,plain,(
% 1.45/0.54    ( ! [X0] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8)),
% 1.45/0.54    inference(subsumption_resolution,[],[f204,f127])).
% 1.45/0.54  fof(f204,plain,(
% 1.45/0.54    ( ! [X0] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7)),
% 1.45/0.54    inference(subsumption_resolution,[],[f203,f122])).
% 1.45/0.54  fof(f203,plain,(
% 1.45/0.54    ( ! [X0] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_4 | ~spl9_6)),
% 1.45/0.54    inference(subsumption_resolution,[],[f197,f117])).
% 1.45/0.54  fof(f197,plain,(
% 1.45/0.54    ( ! [X0] : (~m2_orders_2(X0,sK4,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl9_4),
% 1.45/0.54    inference(resolution,[],[f82,f107])).
% 1.45/0.54  fof(f107,plain,(
% 1.45/0.54    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))) | ~spl9_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f105])).
% 1.45/0.54  fof(f82,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.45/0.54  fof(f511,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10)),
% 1.45/0.54    inference(subsumption_resolution,[],[f510,f137])).
% 1.45/0.54  fof(f510,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4)) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9)),
% 1.45/0.54    inference(subsumption_resolution,[],[f509,f132])).
% 1.45/0.54  fof(f509,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8)),
% 1.45/0.54    inference(subsumption_resolution,[],[f508,f127])).
% 1.45/0.54  fof(f508,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7)),
% 1.45/0.54    inference(subsumption_resolution,[],[f507,f122])).
% 1.45/0.54  fof(f507,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 1.45/0.54    inference(subsumption_resolution,[],[f506,f117])).
% 1.45/0.54  fof(f506,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 1.45/0.54    inference(subsumption_resolution,[],[f505,f112])).
% 1.45/0.54  fof(f505,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (~spl9_2 | ~spl9_4)),
% 1.45/0.54    inference(subsumption_resolution,[],[f503,f107])).
% 1.45/0.54  fof(f503,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_orders_2(sK4,sK5,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK4,sK6) | ~m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl9_2),
% 1.45/0.54    inference(superposition,[],[f88,f97])).
% 1.45/0.54  fof(f97,plain,(
% 1.45/0.54    sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) | ~spl9_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f95])).
% 1.45/0.54  fof(f88,plain,(
% 1.45/0.54    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(equality_resolution,[],[f70])).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f16])).
% 1.45/0.54  fof(f16,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f15])).
% 1.45/0.54  fof(f15,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).
% 1.45/0.54  fof(f415,plain,(
% 1.45/0.54    ~r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) | spl9_42),
% 1.45/0.54    inference(avatar_component_clause,[],[f413])).
% 1.45/0.54  fof(f102,plain,(
% 1.45/0.54    m2_orders_2(sK7,sK4,sK6) | ~spl9_3),
% 1.45/0.54    inference(avatar_component_clause,[],[f100])).
% 1.45/0.54  fof(f488,plain,(
% 1.45/0.54    ~spl9_17 | spl9_27 | ~spl9_31),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f487])).
% 1.45/0.54  fof(f487,plain,(
% 1.45/0.54    $false | (~spl9_17 | spl9_27 | ~spl9_31)),
% 1.45/0.54    inference(subsumption_resolution,[],[f485,f228])).
% 1.45/0.54  fof(f485,plain,(
% 1.45/0.54    ~r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5)) | (spl9_27 | ~spl9_31)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f330,f397,f71])).
% 1.45/0.54  fof(f397,plain,(
% 1.45/0.54    ( ! [X0] : (~sP2(X0,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5,sK4)) ) | spl9_27),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f298,f73])).
% 1.45/0.54  fof(f73,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | r2_orders_2(X3,X1,X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f298,plain,(
% 1.45/0.54    ~r2_orders_2(sK4,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK5) | spl9_27),
% 1.45/0.54    inference(avatar_component_clause,[],[f297])).
% 1.45/0.54  fof(f416,plain,(
% 1.45/0.54    ~spl9_42 | ~spl9_5 | ~spl9_6 | ~spl9_9 | spl9_10 | ~spl9_16 | spl9_39),
% 1.45/0.54    inference(avatar_split_clause,[],[f408,f382,f221,f135,f130,f115,f110,f413])).
% 1.45/0.54  fof(f408,plain,(
% 1.45/0.54    ~r3_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) | (~spl9_5 | ~spl9_6 | ~spl9_9 | spl9_10 | ~spl9_16 | spl9_39)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f137,f132,f117,f112,f223,f384,f84])).
% 1.45/0.54  fof(f84,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f53])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(nnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.45/0.54  fof(f384,plain,(
% 1.45/0.54    ~r1_orders_2(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5))) | spl9_39),
% 1.45/0.54    inference(avatar_component_clause,[],[f382])).
% 1.45/0.54  fof(f331,plain,(
% 1.45/0.54    spl9_31 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | ~spl9_14 | ~spl9_16),
% 1.45/0.54    inference(avatar_split_clause,[],[f314,f221,f199,f135,f130,f125,f120,f115,f110,f328])).
% 1.45/0.54  fof(f199,plain,(
% 1.45/0.54    spl9_14 <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.45/0.54  fof(f314,plain,(
% 1.45/0.54    sP3(sK4,sK5,sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),sK7) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | ~spl9_14 | ~spl9_16)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f223,f112,f201,f76])).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (sP3(X0,X2,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP3(X0,X2,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(definition_folding,[],[f18,f35,f34])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 1.45/0.54  fof(f201,plain,(
% 1.45/0.54    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | ~spl9_14),
% 1.45/0.54    inference(avatar_component_clause,[],[f199])).
% 1.45/0.54  fof(f229,plain,(
% 1.45/0.54    spl9_17 | spl9_1 | ~spl9_15),
% 1.45/0.54    inference(avatar_split_clause,[],[f217,f212,f90,f226])).
% 1.45/0.54  fof(f90,plain,(
% 1.45/0.54    spl9_1 <=> k1_xboole_0 = k3_orders_2(sK4,sK7,sK5)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.45/0.54  fof(f212,plain,(
% 1.45/0.54    spl9_15 <=> m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.45/0.54  fof(f217,plain,(
% 1.45/0.54    r2_hidden(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),k3_orders_2(sK4,sK7,sK5)) | (spl9_1 | ~spl9_15)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f92,f214,f80])).
% 1.45/0.54  fof(f80,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f52])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    ! [X0,X1] : ((r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f51])).
% 1.45/0.54  fof(f51,plain,(
% 1.45/0.54    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),X0)))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(flattening,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.45/0.54  fof(f214,plain,(
% 1.45/0.54    m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl9_15),
% 1.45/0.54    inference(avatar_component_clause,[],[f212])).
% 1.45/0.54  fof(f92,plain,(
% 1.45/0.54    k1_xboole_0 != k3_orders_2(sK4,sK7,sK5) | spl9_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f90])).
% 1.45/0.54  fof(f224,plain,(
% 1.45/0.54    spl9_16 | spl9_1 | ~spl9_15),
% 1.45/0.54    inference(avatar_split_clause,[],[f218,f212,f90,f221])).
% 1.45/0.54  fof(f218,plain,(
% 1.45/0.54    m1_subset_1(sK8(u1_struct_0(sK4),k3_orders_2(sK4,sK7,sK5)),u1_struct_0(sK4)) | (spl9_1 | ~spl9_15)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f92,f214,f79])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    ( ! [X0,X1] : (m1_subset_1(sK8(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f52])).
% 1.45/0.54  fof(f215,plain,(
% 1.45/0.54    spl9_15 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | ~spl9_14),
% 1.45/0.54    inference(avatar_split_clause,[],[f209,f199,f135,f130,f125,f120,f115,f110,f212])).
% 1.45/0.54  fof(f209,plain,(
% 1.45/0.54    m1_subset_1(k3_orders_2(sK4,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10 | ~spl9_14)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f112,f201,f83])).
% 1.45/0.54  fof(f83,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 1.45/0.54  fof(f202,plain,(
% 1.45/0.54    spl9_14 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10),
% 1.45/0.54    inference(avatar_split_clause,[],[f196,f135,f130,f125,f120,f115,f105,f100,f199])).
% 1.45/0.54  fof(f196,plain,(
% 1.45/0.54    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_10)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f117,f102,f107,f82])).
% 1.45/0.54  fof(f161,plain,(
% 1.45/0.54    ~spl9_12 | ~spl9_11),
% 1.45/0.54    inference(avatar_split_clause,[],[f160,f148,f156])).
% 1.45/0.54  fof(f148,plain,(
% 1.45/0.54    spl9_11 <=> sP1(sK4,sK5,sK5)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.45/0.54  fof(f160,plain,(
% 1.45/0.54    ~r2_orders_2(sK4,sK5,sK5) | ~spl9_11),
% 1.45/0.54    inference(subsumption_resolution,[],[f154,f87])).
% 1.45/0.54  fof(f87,plain,(
% 1.45/0.54    ( ! [X2,X1] : (~sP0(X1,X1,X2)) )),
% 1.45/0.54    inference(equality_resolution,[],[f67])).
% 1.45/0.55  fof(f67,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (X0 != X1 | ~sP0(X0,X1,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f45])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2)))),
% 1.45/0.55    inference(rectify,[],[f44])).
% 1.45/0.55  fof(f44,plain,(
% 1.45/0.55    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 1.45/0.55    inference(flattening,[],[f43])).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 1.45/0.55    inference(nnf_transformation,[],[f31])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 1.45/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/0.55  fof(f154,plain,(
% 1.45/0.55    ~r2_orders_2(sK4,sK5,sK5) | sP0(sK5,sK5,sK4) | ~spl9_11),
% 1.45/0.55    inference(resolution,[],[f150,f64])).
% 1.45/0.55  fof(f64,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f42])).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 1.45/0.55    inference(nnf_transformation,[],[f32])).
% 1.45/0.55  fof(f32,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1,X2))),
% 1.45/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.45/0.55  fof(f150,plain,(
% 1.45/0.55    sP1(sK4,sK5,sK5) | ~spl9_11),
% 1.45/0.55    inference(avatar_component_clause,[],[f148])).
% 1.45/0.55  fof(f151,plain,(
% 1.45/0.55    spl9_11 | ~spl9_5 | ~spl9_6),
% 1.45/0.55    inference(avatar_split_clause,[],[f144,f115,f110,f148])).
% 1.45/0.55  fof(f144,plain,(
% 1.45/0.55    sP1(sK4,sK5,sK5) | (~spl9_5 | ~spl9_6)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f117,f112,f112,f69])).
% 1.45/0.55  fof(f69,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f33])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.45/0.55    inference(definition_folding,[],[f14,f32,f31])).
% 1.45/0.55  % (5854)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.45/0.55  fof(f14,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f3])).
% 1.45/0.55  fof(f3,axiom,(
% 1.45/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 1.45/0.55  fof(f138,plain,(
% 1.45/0.55    ~spl9_10),
% 1.45/0.55    inference(avatar_split_clause,[],[f54,f135])).
% 1.45/0.55  fof(f54,plain,(
% 1.45/0.55    ~v2_struct_0(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    (((k1_xboole_0 != k3_orders_2(sK4,sK7,sK5) & sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) & m2_orders_2(sK7,sK4,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f40,f39,f38,f37])).
% 1.45/0.55  fof(f37,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,X1) & k1_funct_1(X2,u1_struct_0(sK4)) = X1 & m2_orders_2(X3,sK4,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4)))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,X1) & k1_funct_1(X2,u1_struct_0(sK4)) = X1 & m2_orders_2(X3,sK4,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4)))) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,sK5) & k1_funct_1(X2,u1_struct_0(sK4)) = sK5 & m2_orders_2(X3,sK4,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,sK5) & k1_funct_1(X2,u1_struct_0(sK4)) = sK5 & m2_orders_2(X3,sK4,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK4)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,sK5) & sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) & m2_orders_2(X3,sK4,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4))))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ? [X3] : (k1_xboole_0 != k3_orders_2(sK4,X3,sK5) & sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) & m2_orders_2(X3,sK4,sK6)) => (k1_xboole_0 != k3_orders_2(sK4,sK7,sK5) & sK5 = k1_funct_1(sK6,u1_struct_0(sK4)) & m2_orders_2(sK7,sK4,sK6))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f13,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f12])).
% 1.45/0.55  fof(f12,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,negated_conjecture,(
% 1.45/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 1.45/0.55    inference(negated_conjecture,[],[f10])).
% 1.45/0.55  fof(f10,conjecture,(
% 1.45/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).
% 1.45/0.55  fof(f133,plain,(
% 1.45/0.55    spl9_9),
% 1.45/0.55    inference(avatar_split_clause,[],[f55,f130])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    v3_orders_2(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f128,plain,(
% 1.45/0.55    spl9_8),
% 1.45/0.55    inference(avatar_split_clause,[],[f56,f125])).
% 1.45/0.55  fof(f56,plain,(
% 1.45/0.55    v4_orders_2(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f123,plain,(
% 1.45/0.55    spl9_7),
% 1.45/0.55    inference(avatar_split_clause,[],[f57,f120])).
% 1.45/0.55  fof(f57,plain,(
% 1.45/0.55    v5_orders_2(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f118,plain,(
% 1.45/0.55    spl9_6),
% 1.45/0.55    inference(avatar_split_clause,[],[f58,f115])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    l1_orders_2(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f113,plain,(
% 1.45/0.55    spl9_5),
% 1.45/0.55    inference(avatar_split_clause,[],[f59,f110])).
% 1.45/0.55  fof(f59,plain,(
% 1.45/0.55    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f108,plain,(
% 1.45/0.55    spl9_4),
% 1.45/0.55    inference(avatar_split_clause,[],[f60,f105])).
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK4)))),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f103,plain,(
% 1.45/0.55    spl9_3),
% 1.45/0.55    inference(avatar_split_clause,[],[f61,f100])).
% 1.45/0.55  fof(f61,plain,(
% 1.45/0.55    m2_orders_2(sK7,sK4,sK6)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f98,plain,(
% 1.45/0.55    spl9_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f62,f95])).
% 1.45/0.55  fof(f62,plain,(
% 1.45/0.55    sK5 = k1_funct_1(sK6,u1_struct_0(sK4))),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    ~spl9_1),
% 1.45/0.55    inference(avatar_split_clause,[],[f63,f90])).
% 1.45/0.55  fof(f63,plain,(
% 1.45/0.55    k1_xboole_0 != k3_orders_2(sK4,sK7,sK5)),
% 1.45/0.55    inference(cnf_transformation,[],[f41])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (5861)------------------------------
% 1.45/0.55  % (5861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (5861)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (5861)Memory used [KB]: 11129
% 1.45/0.55  % (5861)Time elapsed: 0.111 s
% 1.45/0.55  % (5861)------------------------------
% 1.45/0.55  % (5861)------------------------------
% 1.45/0.55  % (5844)Success in time 0.184 s
%------------------------------------------------------------------------------
