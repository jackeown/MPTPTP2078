%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 360 expanded)
%              Number of leaves         :   45 ( 162 expanded)
%              Depth                    :    9
%              Number of atoms          :  602 (1206 expanded)
%              Number of equality atoms :   74 ( 150 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f123,f154,f160,f168,f175,f180,f190,f197,f207,f243,f271,f285,f299,f333,f346,f369,f414,f454,f459,f464,f654,f720,f763])).

fof(f763,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | ~ spl6_44
    | ~ spl6_62
    | spl6_64 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_44
    | ~ spl6_62
    | spl6_64 ),
    inference(subsumption_resolution,[],[f761,f719])).

fof(f719,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | spl6_64 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl6_64
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(k1_tex_2(sK3,sK5(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f761,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_44
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f742,f653])).

fof(f653,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK3,sK5(sK4)))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl6_62
  <=> u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f742,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK5(sK4))),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_44
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f109,f94,f463,f653,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X2) != u1_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X2) != u1_struct_0(X1)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X2) != u1_struct_0(X1)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X2) = u1_struct_0(X1)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f463,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK5(sK4)),sK3)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl6_44
  <=> m1_pre_topc(k1_tex_2(sK3,sK5(sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f94,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_1
  <=> m1_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f109,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f720,plain,
    ( ~ spl6_64
    | spl6_27
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f715,f651,f296,f717])).

fof(f296,plain,
    ( spl6_27
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK5(sK4))),u1_pre_topc(k1_tex_2(sK3,sK5(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f715,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | spl6_27
    | ~ spl6_62 ),
    inference(backward_demodulation,[],[f298,f653])).

fof(f298,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK5(sK4))),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f296])).

fof(f654,plain,
    ( spl6_62
    | ~ spl6_4
    | spl6_5
    | ~ spl6_25
    | ~ spl6_34
    | spl6_42
    | ~ spl6_43
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f649,f461,f456,f451,f366,f282,f112,f107,f651])).

fof(f112,plain,
    ( spl6_5
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f282,plain,
    ( spl6_25
  <=> m1_subset_1(sK5(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f366,plain,
    ( spl6_34
  <=> u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK3),sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f451,plain,
    ( spl6_42
  <=> v2_struct_0(k1_tex_2(sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f456,plain,
    ( spl6_43
  <=> v1_pre_topc(k1_tex_2(sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f649,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK3,sK5(sK4)))
    | ~ spl6_4
    | spl6_5
    | ~ spl6_25
    | ~ spl6_34
    | spl6_42
    | ~ spl6_43
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f626,f368])).

fof(f368,plain,
    ( u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK3),sK5(sK4))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f366])).

fof(f626,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK5(sK4))) = k6_domain_1(u1_struct_0(sK3),sK5(sK4))
    | ~ spl6_4
    | spl6_5
    | ~ spl6_25
    | spl6_42
    | ~ spl6_43
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f114,f109,f284,f453,f458,f463,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2) )
                & ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f458,plain,
    ( v1_pre_topc(k1_tex_2(sK3,sK5(sK4)))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f456])).

fof(f453,plain,
    ( ~ v2_struct_0(k1_tex_2(sK3,sK5(sK4)))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f451])).

fof(f284,plain,
    ( m1_subset_1(sK5(sK4),u1_struct_0(sK3))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f282])).

fof(f114,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f464,plain,
    ( spl6_44
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f447,f398,f461])).

fof(f398,plain,
    ( spl6_35
  <=> sP2(sK3,sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f447,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK5(sK4)),sK3)
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f400,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f400,plain,
    ( sP2(sK3,sK5(sK4))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f398])).

fof(f459,plain,
    ( spl6_43
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f448,f398,f456])).

fof(f448,plain,
    ( v1_pre_topc(k1_tex_2(sK3,sK5(sK4)))
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f400,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f454,plain,
    ( ~ spl6_42
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f449,f398,f451])).

fof(f449,plain,
    ( ~ v2_struct_0(k1_tex_2(sK3,sK5(sK4)))
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f400,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f414,plain,
    ( spl6_35
    | ~ spl6_4
    | spl6_5
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f413,f282,f112,f107,f398])).

fof(f413,plain,
    ( sP2(sK3,sK5(sK4))
    | ~ spl6_4
    | spl6_5
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f412,f114])).

fof(f412,plain,
    ( sP2(sK3,sK5(sK4))
    | v2_struct_0(sK3)
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f396,f109])).

fof(f396,plain,
    ( sP2(sK3,sK5(sK4))
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl6_25 ),
    inference(resolution,[],[f83,f284])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f44])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f369,plain,
    ( spl6_34
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f364,f336,f330,f366])).

fof(f330,plain,
    ( spl6_30
  <=> k1_tarski(sK5(sK4)) = k6_domain_1(u1_struct_0(sK3),sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f336,plain,
    ( spl6_31
  <=> u1_struct_0(sK4) = k1_tarski(sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f364,plain,
    ( u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK3),sK5(sK4))
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f332,f338])).

fof(f338,plain,
    ( u1_struct_0(sK4) = k1_tarski(sK5(sK4))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f336])).

fof(f332,plain,
    ( k1_tarski(sK5(sK4)) = k6_domain_1(u1_struct_0(sK3),sK5(sK4))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f330])).

fof(f346,plain,
    ( spl6_31
    | spl6_14
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f345,f240,f194,f177,f336])).

fof(f177,plain,
    ( spl6_14
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f194,plain,
    ( spl6_16
  <=> m1_subset_1(sK5(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f240,plain,
    ( spl6_20
  <=> u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK4),sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f345,plain,
    ( u1_struct_0(sK4) = k1_tarski(sK5(sK4))
    | spl6_14
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f344,f179])).

fof(f179,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f344,plain,
    ( u1_struct_0(sK4) = k1_tarski(sK5(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f328,f196])).

fof(f196,plain,
    ( m1_subset_1(sK5(sK4),u1_struct_0(sK4))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f328,plain,
    ( u1_struct_0(sK4) = k1_tarski(sK5(sK4))
    | ~ m1_subset_1(sK5(sK4),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl6_20 ),
    inference(superposition,[],[f242,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f242,plain,
    ( u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK4),sK5(sK4))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f333,plain,
    ( spl6_30
    | spl6_11
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f324,f282,f157,f330])).

fof(f157,plain,
    ( spl6_11
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f324,plain,
    ( k1_tarski(sK5(sK4)) = k6_domain_1(u1_struct_0(sK3),sK5(sK4))
    | spl6_11
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f159,f284,f79])).

fof(f159,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f299,plain,
    ( ~ spl6_27
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f288,f282,f296])).

fof(f288,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK5(sK4))),u1_pre_topc(k1_tex_2(sK3,sK5(sK4))))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f284,f63])).

fof(f63,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    & m1_pre_topc(sK4,sK3)
    & v7_struct_0(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_pre_topc(X1,sK3)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_pre_topc(X1,sK3)
        & v7_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
          | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_pre_topc(sK4,sK3)
      & v7_struct_0(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).

fof(f285,plain,
    ( spl6_25
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f272,f268,f204,f282])).

fof(f204,plain,
    ( spl6_17
  <=> r2_hidden(sK5(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f268,plain,
    ( spl6_23
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f272,plain,
    ( m1_subset_1(sK5(sK4),u1_struct_0(sK3))
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f206,f270,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f270,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f268])).

fof(f206,plain,
    ( r2_hidden(sK5(sK4),u1_struct_0(sK4))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f271,plain,
    ( spl6_23
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f264,f107,f92,f268])).

fof(f264,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f109,f94,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

fof(f243,plain,
    ( spl6_20
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f238,f185,f240])).

fof(f185,plain,
    ( spl6_15
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f238,plain,
    ( u1_struct_0(sK4) = k6_domain_1(u1_struct_0(sK4),sK5(sK4))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f187,f72])).

fof(f72,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))
          & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f187,plain,
    ( sP0(sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f207,plain,
    ( spl6_17
    | spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f200,f194,f177,f204])).

fof(f200,plain,
    ( r2_hidden(sK5(sK4),u1_struct_0(sK4))
    | spl6_14
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f196,f179,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f197,plain,
    ( spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f192,f185,f194])).

fof(f192,plain,
    ( m1_subset_1(sK5(sK4),u1_struct_0(sK4))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f187,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f190,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f189,f172,f97,f185])).

fof(f97,plain,
    ( spl6_2
  <=> v7_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f172,plain,
    ( spl6_13
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f189,plain,
    ( sP0(sK4)
    | ~ spl6_2
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f99,plain,
    ( v7_struct_0(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f183,plain,
    ( ~ v7_struct_0(sK4)
    | sP0(sK4)
    | ~ spl6_13 ),
    inference(resolution,[],[f174,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v7_struct_0(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v7_struct_0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f174,plain,
    ( sP1(sK4)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f180,plain,
    ( ~ spl6_14
    | spl6_3
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f169,f164,f102,f177])).

fof(f102,plain,
    ( spl6_3
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f164,plain,
    ( spl6_12
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f169,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl6_3
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f104,f166,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f166,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f104,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f175,plain,
    ( spl6_13
    | spl6_3
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f170,f164,f102,f172])).

fof(f170,plain,
    ( sP1(sK4)
    | spl6_3
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f104,f166,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f42,f41])).

fof(f28,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).

fof(f168,plain,
    ( spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f162,f149,f164])).

fof(f149,plain,
    ( spl6_10
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f162,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_10 ),
    inference(resolution,[],[f151,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f151,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f160,plain,
    ( ~ spl6_11
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f155,f119,f112,f157])).

fof(f119,plain,
    ( spl6_6
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f155,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f114,f121,f68])).

fof(f121,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f154,plain,
    ( spl6_10
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f153,f107,f92,f149])).

fof(f153,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f147,f109])).

fof(f147,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ spl6_1 ),
    inference(resolution,[],[f65,f94])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f123,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f117,f107,f119])).

fof(f117,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f64,f109])).

fof(f115,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f59,f107])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f60,f102])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f61,f97])).

fof(f61,plain,(
    v7_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f62,f92])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

%------------------------------------------------------------------------------
