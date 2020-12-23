%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 428 expanded)
%              Number of leaves         :   36 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  686 (1408 expanded)
%              Number of equality atoms :   69 ( 116 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f75,f79,f91,f98,f123,f127,f131,f135,f157,f161,f183,f190,f194,f200,f204,f228,f249,f267,f276,f290,f307,f308])).

fof(f308,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | k1_tarski(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | u1_struct_0(sK1) != k1_tarski(sK2(sK1))
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f307,plain,
    ( spl3_35
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | spl3_15
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f214,f202,f181,f159,f133,f64,f60,f305])).

fof(f305,plain,
    ( spl3_35
  <=> u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f60,plain,
    ( spl3_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( spl3_13
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f159,plain,
    ( spl3_15
  <=> v2_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f181,plain,
    ( spl3_16
  <=> v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f202,plain,
    ( spl3_21
  <=> m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f214,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | spl3_15
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f61,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f213,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_4
    | ~ spl3_13
    | spl3_15
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f212,f182])).

fof(f182,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f212,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_4
    | ~ spl3_13
    | spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f211,f160])).

fof(f160,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f211,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f210,f134])).

fof(f134,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f210,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f205,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_21 ),
    inference(resolution,[],[f203,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f203,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f202])).

fof(f290,plain,
    ( ~ spl3_32
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f215,f202,f133,f77,f64,f288])).

fof(f288,plain,
    ( spl3_32
  <=> u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f77,plain,
    ( spl3_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f215,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f206,f137])).

fof(f137,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))
    | ~ spl3_13 ),
    inference(resolution,[],[f134,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f206,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(resolution,[],[f203,f87])).

fof(f87,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) != u1_struct_0(sK1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f82,f65])).

fof(f82,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) != u1_struct_0(sK1)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X1) != u1_struct_0(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f78,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f276,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f274,f61])).

fof(f274,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f273,f74])).

fof(f74,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f273,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_28 ),
    inference(resolution,[],[f266,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f266,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl3_28
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f267,plain,
    ( spl3_27
    | spl3_28
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f143,f133,f265,f262])).

fof(f262,plain,
    ( spl3_27
  <=> k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f134,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f249,plain,
    ( ~ spl3_17
    | spl3_10
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f237,f226,f198,f121,f185])).

fof(f185,plain,
    ( spl3_17
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f121,plain,
    ( spl3_10
  <=> v2_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f198,plain,
    ( spl3_20
  <=> l1_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f226,plain,
    ( spl3_23
  <=> u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f237,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_10
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f236,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f236,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f230,f199])).

fof(f199,plain,
    ( l1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f230,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_23 ),
    inference(superposition,[],[f47,f227])).

fof(f227,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,
    ( spl3_23
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f171,f155,f129,f125,f121,f96,f89,f52,f226])).

fof(f52,plain,
    ( spl3_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f89,plain,
    ( spl3_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f96,plain,
    ( spl3_8
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f125,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f129,plain,
    ( spl3_12
  <=> v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f155,plain,
    ( spl3_14
  <=> m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f171,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f170,f126])).

fof(f126,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f170,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f169,plain,
    ( v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f168,f130])).

fof(f130,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f168,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f167,f122])).

fof(f167,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f166,f97])).

fof(f97,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f162,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_14 ),
    inference(resolution,[],[f156,f50])).

fof(f156,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f204,plain,
    ( spl3_21
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f153,f133,f64,f60,f202])).

fof(f153,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f152,f61])).

fof(f152,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f142,f65])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | ~ spl3_13 ),
    inference(resolution,[],[f134,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f200,plain,
    ( spl3_20
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f196,f192,f198])).

fof(f192,plain,
    ( spl3_19
  <=> l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f196,plain,
    ( l1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_19 ),
    inference(resolution,[],[f193,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f193,plain,
    ( l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f172,f155,f89,f192])).

fof(f172,plain,
    ( l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f163,f90])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_14 ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f190,plain,
    ( spl3_17
    | spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f118,f96,f89,f56,f52,f188,f185])).

fof(f188,plain,
    ( spl3_18
  <=> u1_struct_0(sK1) = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f56,plain,
    ( spl3_2
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( u1_struct_0(sK1) = k1_tarski(sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f108,f93])).

fof(f93,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f70,f92])).

fof(f92,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f90,f48])).

fof(f70,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f68,f53])).

fof(f68,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).

fof(f57,plain,
    ( v7_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl3_8 ),
    inference(resolution,[],[f97,f49])).

fof(f183,plain,
    ( spl3_16
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f133,f64,f60,f181])).

fof(f151,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f150,f61])).

fof(f150,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f141,f65])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_13 ),
    inference(resolution,[],[f134,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f161,plain,
    ( ~ spl3_15
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f149,f133,f64,f60,f159])).

fof(f149,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f148,f61])).

fof(f148,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f140,f65])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ spl3_13 ),
    inference(resolution,[],[f134,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f157,plain,
    ( spl3_14
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f117,f96,f89,f52,f155])).

fof(f117,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f116,f53])).

fof(f116,plain,
    ( v2_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f97,f38])).

fof(f135,plain,
    ( spl3_13
    | spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f119,f96,f77,f64,f60,f52,f133])).

fof(f119,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f86,f97])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f85,f61])).

fof(f85,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f84,f53])).

fof(f84,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f81,f65])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f131,plain,
    ( spl3_12
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f115,f96,f89,f52,f129])).

fof(f115,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f114,plain,
    ( v2_struct_0(sK1)
    | v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_8 ),
    inference(resolution,[],[f97,f37])).

fof(f127,plain,
    ( spl3_11
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f93,f89,f56,f52,f125])).

fof(f123,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f113,f96,f89,f52,f121])).

fof(f113,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f112,f53])).

fof(f112,plain,
    ( v2_struct_0(sK1)
    | ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f105,f90])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ spl3_8 ),
    inference(resolution,[],[f97,f36])).

fof(f98,plain,
    ( spl3_8
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f94,f89,f56,f52,f96])).

fof(f94,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f69,f92])).

fof(f69,plain,
    ( ~ l1_struct_0(sK1)
    | m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f67,f53])).

fof(f67,plain,
    ( ~ l1_struct_0(sK1)
    | m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f83,f77,f64,f89])).

fof(f83,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f80,f65])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f78,f43])).

fof(f79,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f64,f73])).

fof(f71,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f65,f48])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (12144)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (12148)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (12148)Refutation not found, incomplete strategy% (12148)------------------------------
% 0.21/0.48  % (12148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12143)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (12140)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (12142)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (12156)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (12148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12148)Memory used [KB]: 6268
% 0.21/0.49  % (12148)Time elapsed: 0.054 s
% 0.21/0.49  % (12148)------------------------------
% 0.21/0.49  % (12148)------------------------------
% 0.21/0.49  % (12150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (12152)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (12145)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (12138)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (12158)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (12146)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (12158)Refutation not found, incomplete strategy% (12158)------------------------------
% 0.21/0.50  % (12158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12158)Memory used [KB]: 10618
% 0.21/0.50  % (12158)Time elapsed: 0.002 s
% 0.21/0.50  % (12158)------------------------------
% 0.21/0.50  % (12158)------------------------------
% 0.21/0.50  % (12138)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f75,f79,f91,f98,f123,f127,f131,f135,f157,f161,f183,f190,f194,f200,f204,f228,f249,f267,f276,f290,f307,f308])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | k1_tarski(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | u1_struct_0(sK1) != k1_tarski(sK2(sK1)) | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl3_35 | spl3_3 | ~spl3_4 | ~spl3_13 | spl3_15 | ~spl3_16 | ~spl3_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f202,f181,f159,f133,f64,f60,f305])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    spl3_35 <=> u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl3_3 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl3_13 <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl3_15 <=> v2_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    spl3_16 <=> v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl3_21 <=> m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_13 | spl3_15 | ~spl3_16 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f213,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | (~spl3_4 | ~spl3_13 | spl3_15 | ~spl3_16 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f182])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f181])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | (~spl3_4 | ~spl3_13 | spl3_15 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f211,f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | (~spl3_4 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f133])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | (~spl3_4 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~spl3_21),
% 0.21/0.50    inference(resolution,[],[f203,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | ~spl3_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    ~spl3_32 | ~spl3_4 | ~spl3_6 | ~spl3_13 | ~spl3_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f215,f202,f133,f77,f64,f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl3_32 <=> u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl3_6 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | (~spl3_4 | ~spl3_6 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f134,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) | (~spl3_4 | ~spl3_6 | ~spl3_21)),
% 0.21/0.50    inference(resolution,[],[f203,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) != u1_struct_0(sK1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f82,f65])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | u1_struct_0(X1) != u1_struct_0(sK1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f78,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | u1_struct_0(X1) != u1_struct_0(X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl3_3 | ~spl3_5 | ~spl3_28),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    $false | (spl3_3 | ~spl3_5 | ~spl3_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f274,f61])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    v2_struct_0(sK0) | (~spl3_5 | ~spl3_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f273,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_28),
% 0.21/0.50    inference(resolution,[],[f266,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    spl3_28 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl3_27 | spl3_28 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f143,f133,f265,f262])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl3_27 <=> k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f134,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~spl3_17 | spl3_10 | ~spl3_20 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f237,f226,f198,f121,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl3_17 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl3_10 <=> v2_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl3_20 <=> l1_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    spl3_23 <=> u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK1)) | (spl3_10 | ~spl3_20 | ~spl3_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_20 | ~spl3_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f230,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    l1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f198])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_23),
% 0.21/0.50    inference(superposition,[],[f47,f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f226])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    spl3_23 | spl3_1 | ~spl3_7 | ~spl3_8 | spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f155,f129,f125,f121,f96,f89,f52,f226])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_1 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_7 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl3_8 <=> m1_subset_1(sK2(sK1),u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl3_11 <=> u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl3_12 <=> v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl3_14 <=> m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (spl3_1 | ~spl3_7 | ~spl3_8 | spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f170,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (spl3_1 | ~spl3_7 | ~spl3_8 | spl3_10 | ~spl3_12 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f169,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    v2_struct_0(sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_8 | spl3_10 | ~spl3_12 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_8 | spl3_10 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f122])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_8 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ~m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_14),
% 0.21/0.50    inference(resolution,[],[f156,f50])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f155])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl3_21 | spl3_3 | ~spl3_4 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f133,f64,f60,f202])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | (spl3_3 | ~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f61])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | (~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f65])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f134,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl3_20 | ~spl3_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f196,f192,f198])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl3_19 <=> l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    l1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_19),
% 0.21/0.50    inference(resolution,[],[f193,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~spl3_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f192])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl3_19 | ~spl3_7 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f172,f155,f89,f192])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f90])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~spl3_14),
% 0.21/0.50    inference(resolution,[],[f156,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl3_17 | spl3_18 | spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f118,f96,f89,f56,f52,f188,f185])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl3_18 <=> u1_struct_0(sK1) = k1_tarski(sK2(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl3_2 <=> v7_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k1_tarski(sK2(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | (spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f108,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | (spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.50    inference(resolution,[],[f90,f48])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | (spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f68,f53])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | v2_struct_0(sK1) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f57,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v7_struct_0(sK1) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = k1_tarski(sK2(sK1)) | ~spl3_8),
% 0.21/0.50    inference(resolution,[],[f97,f49])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl3_16 | spl3_3 | ~spl3_4 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f151,f133,f64,f60,f181])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | (spl3_3 | ~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f61])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | (~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f141,f65])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f134,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k1_tex_2(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~spl3_15 | spl3_3 | ~spl3_4 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f149,f133,f64,f60,f159])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | (spl3_3 | ~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f61])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | (~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f140,f65])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f134,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_14 | spl3_1 | ~spl3_7 | ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f117,f96,f89,f52,f155])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | (spl3_1 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f116,f53])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    v2_struct_0(sK1) | m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | (~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f90])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | ~spl3_8),
% 0.21/0.50    inference(resolution,[],[f97,f38])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl3_13 | spl3_1 | spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f96,f77,f64,f60,f52,f133])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | (spl3_1 | spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_8)),
% 0.21/0.51    inference(resolution,[],[f86,f97])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl3_1 | spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f61])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f53])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f65])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_6),
% 0.21/0.51    inference(resolution,[],[f78,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl3_12 | spl3_1 | ~spl3_7 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f115,f96,f89,f52,f129])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | (spl3_1 | ~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f53])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v2_struct_0(sK1) | v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f90])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~spl3_8),
% 0.21/0.51    inference(resolution,[],[f97,f37])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl3_11 | spl3_1 | ~spl3_2 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f93,f89,f56,f52,f125])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~spl3_10 | spl3_1 | ~spl3_7 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f113,f96,f89,f52,f121])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | (spl3_1 | ~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f53])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f90])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~spl3_8),
% 0.21/0.51    inference(resolution,[],[f97,f36])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl3_8 | spl3_1 | ~spl3_2 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f89,f56,f52,f96])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | (spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f92])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~l1_struct_0(sK1) | m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | (spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f67,f53])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~l1_struct_0(sK1) | m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f57,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl3_7 | ~spl3_4 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f83,f77,f64,f89])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | (~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f65])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK1) | ~spl3_6),
% 0.21/0.51    inference(resolution,[],[f78,f43])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl3_5 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f64,f73])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f65,f48])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f64])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f60])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f56])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v7_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f52])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12138)------------------------------
% 0.21/0.51  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12138)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12138)Memory used [KB]: 6268
% 0.21/0.51  % (12138)Time elapsed: 0.076 s
% 0.21/0.51  % (12138)------------------------------
% 0.21/0.51  % (12138)------------------------------
% 0.21/0.51  % (12137)Success in time 0.148 s
%------------------------------------------------------------------------------
