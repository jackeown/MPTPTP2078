%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1718+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 9.05s
% Output     : Refutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 402 expanded)
%              Number of leaves         :   31 ( 197 expanded)
%              Depth                    :   11
%              Number of atoms          :  586 (3267 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5340,f5345,f5350,f5355,f5360,f5365,f5370,f5375,f5380,f5385,f5390,f5395,f5400,f5405,f6316,f6323,f7526,f8489,f11328,f11385,f12634])).

fof(f12634,plain,
    ( ~ spl214_2
    | ~ spl214_3
    | spl214_14
    | ~ spl214_59
    | ~ spl214_60
    | ~ spl214_88
    | ~ spl214_91
    | ~ spl214_150
    | ~ spl214_153 ),
    inference(avatar_contradiction_clause,[],[f12633])).

fof(f12633,plain,
    ( $false
    | ~ spl214_2
    | ~ spl214_3
    | spl214_14
    | ~ spl214_59
    | ~ spl214_60
    | ~ spl214_88
    | ~ spl214_91
    | ~ spl214_150
    | ~ spl214_153 ),
    inference(subsumption_resolution,[],[f12632,f8690])).

fof(f8690,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))
    | ~ spl214_2
    | ~ spl214_3
    | spl214_14
    | ~ spl214_88
    | ~ spl214_91 ),
    inference(unit_resulting_resolution,[],[f5344,f5349,f7525,f5404,f8488,f4220])).

fof(f4220,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3883])).

fof(f3883,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3410])).

fof(f3410,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3409])).

fof(f3409,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3367])).

fof(f3367,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f8488,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl214_91 ),
    inference(avatar_component_clause,[],[f8486])).

fof(f8486,plain,
    ( spl214_91
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_91])])).

fof(f5404,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
    | spl214_14 ),
    inference(avatar_component_clause,[],[f5402])).

fof(f5402,plain,
    ( spl214_14
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_14])])).

fof(f7525,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl214_88 ),
    inference(avatar_component_clause,[],[f7523])).

fof(f7523,plain,
    ( spl214_88
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_88])])).

fof(f5349,plain,
    ( l1_pre_topc(sK0)
    | ~ spl214_3 ),
    inference(avatar_component_clause,[],[f5347])).

fof(f5347,plain,
    ( spl214_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_3])])).

fof(f5344,plain,
    ( v2_pre_topc(sK0)
    | ~ spl214_2 ),
    inference(avatar_component_clause,[],[f5342])).

fof(f5342,plain,
    ( spl214_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_2])])).

fof(f12632,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))
    | ~ spl214_59
    | ~ spl214_60
    | ~ spl214_150
    | ~ spl214_153 ),
    inference(forward_demodulation,[],[f12631,f11327])).

fof(f11327,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl214_150 ),
    inference(avatar_component_clause,[],[f11325])).

fof(f11325,plain,
    ( spl214_150
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_150])])).

fof(f12631,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))
    | ~ spl214_59
    | ~ spl214_60
    | ~ spl214_153 ),
    inference(forward_demodulation,[],[f12630,f4321])).

fof(f4321,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f12630,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))
    | ~ spl214_59
    | ~ spl214_60
    | ~ spl214_153 ),
    inference(forward_demodulation,[],[f12629,f11384])).

fof(f11384,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl214_153 ),
    inference(avatar_component_clause,[],[f11382])).

fof(f11382,plain,
    ( spl214_153
  <=> u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_153])])).

fof(f12629,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)))
    | ~ spl214_59
    | ~ spl214_60 ),
    inference(forward_demodulation,[],[f12610,f4321])).

fof(f12610,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)),k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)))
    | ~ spl214_59
    | ~ spl214_60 ),
    inference(unit_resulting_resolution,[],[f6322,f6315,f4279])).

fof(f4279,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f3450])).

fof(f3450,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f3449])).

fof(f3449,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f6315,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl214_59 ),
    inference(avatar_component_clause,[],[f6313])).

fof(f6313,plain,
    ( spl214_59
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_59])])).

fof(f6322,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl214_60 ),
    inference(avatar_component_clause,[],[f6320])).

fof(f6320,plain,
    ( spl214_60
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_60])])).

fof(f11385,plain,
    ( spl214_153
    | spl214_1
    | ~ spl214_3
    | spl214_5
    | spl214_7
    | ~ spl214_9
    | ~ spl214_11 ),
    inference(avatar_split_clause,[],[f5747,f5387,f5377,f5367,f5357,f5347,f5337,f11382])).

fof(f5337,plain,
    ( spl214_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_1])])).

fof(f5357,plain,
    ( spl214_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_5])])).

fof(f5367,plain,
    ( spl214_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_7])])).

fof(f5377,plain,
    ( spl214_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_9])])).

fof(f5387,plain,
    ( spl214_11
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_11])])).

fof(f5747,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | spl214_1
    | ~ spl214_3
    | spl214_5
    | spl214_7
    | ~ spl214_9
    | ~ spl214_11 ),
    inference(unit_resulting_resolution,[],[f5339,f5349,f5359,f5379,f5369,f5389,f5267])).

fof(f5267,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f5266,f4192])).

fof(f4192,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3388])).

fof(f3388,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3387])).

fof(f3387,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f5266,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f5265,f4193])).

fof(f4193,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3388])).

fof(f5265,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4956,f4194])).

fof(f4194,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3388])).

fof(f4956,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4218])).

fof(f4218,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3882])).

fof(f3882,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3408])).

fof(f3408,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3407])).

fof(f3407,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3326])).

fof(f3326,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f5389,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl214_11 ),
    inference(avatar_component_clause,[],[f5387])).

fof(f5369,plain,
    ( ~ v2_struct_0(sK4)
    | spl214_7 ),
    inference(avatar_component_clause,[],[f5367])).

fof(f5379,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl214_9 ),
    inference(avatar_component_clause,[],[f5377])).

fof(f5359,plain,
    ( ~ v2_struct_0(sK2)
    | spl214_5 ),
    inference(avatar_component_clause,[],[f5357])).

fof(f5339,plain,
    ( ~ v2_struct_0(sK0)
    | spl214_1 ),
    inference(avatar_component_clause,[],[f5337])).

fof(f11328,plain,
    ( spl214_150
    | spl214_1
    | ~ spl214_3
    | spl214_4
    | spl214_6
    | ~ spl214_8
    | ~ spl214_10 ),
    inference(avatar_split_clause,[],[f5741,f5382,f5372,f5362,f5352,f5347,f5337,f11325])).

fof(f5352,plain,
    ( spl214_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_4])])).

fof(f5362,plain,
    ( spl214_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_6])])).

fof(f5372,plain,
    ( spl214_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_8])])).

fof(f5382,plain,
    ( spl214_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_10])])).

fof(f5741,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl214_1
    | ~ spl214_3
    | spl214_4
    | spl214_6
    | ~ spl214_8
    | ~ spl214_10 ),
    inference(unit_resulting_resolution,[],[f5339,f5349,f5354,f5374,f5364,f5384,f5267])).

fof(f5384,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl214_10 ),
    inference(avatar_component_clause,[],[f5382])).

fof(f5364,plain,
    ( ~ v2_struct_0(sK3)
    | spl214_6 ),
    inference(avatar_component_clause,[],[f5362])).

fof(f5374,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl214_8 ),
    inference(avatar_component_clause,[],[f5372])).

fof(f5354,plain,
    ( ~ v2_struct_0(sK1)
    | spl214_4 ),
    inference(avatar_component_clause,[],[f5352])).

fof(f8489,plain,
    ( spl214_91
    | spl214_1
    | ~ spl214_3
    | spl214_5
    | spl214_7
    | ~ spl214_9
    | ~ spl214_11 ),
    inference(avatar_split_clause,[],[f5533,f5387,f5377,f5367,f5357,f5347,f5337,f8486])).

fof(f5533,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | spl214_1
    | ~ spl214_3
    | spl214_5
    | spl214_7
    | ~ spl214_9
    | ~ spl214_11 ),
    inference(unit_resulting_resolution,[],[f5339,f5349,f5359,f5379,f5369,f5389,f4194])).

fof(f7526,plain,
    ( spl214_88
    | spl214_1
    | ~ spl214_3
    | spl214_4
    | spl214_6
    | ~ spl214_8
    | ~ spl214_10 ),
    inference(avatar_split_clause,[],[f5527,f5382,f5372,f5362,f5352,f5347,f5337,f7523])).

fof(f5527,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl214_1
    | ~ spl214_3
    | spl214_4
    | spl214_6
    | ~ spl214_8
    | ~ spl214_10 ),
    inference(unit_resulting_resolution,[],[f5339,f5349,f5354,f5374,f5364,f5384,f4194])).

fof(f6323,plain,
    ( spl214_60
    | ~ spl214_2
    | ~ spl214_3
    | ~ spl214_10
    | ~ spl214_11
    | ~ spl214_13 ),
    inference(avatar_split_clause,[],[f5455,f5397,f5387,f5382,f5347,f5342,f6320])).

fof(f5397,plain,
    ( spl214_13
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_13])])).

fof(f5455,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl214_2
    | ~ spl214_3
    | ~ spl214_10
    | ~ spl214_11
    | ~ spl214_13 ),
    inference(unit_resulting_resolution,[],[f5344,f5349,f5384,f5389,f5399,f4221])).

fof(f4221,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f3883])).

fof(f5399,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl214_13 ),
    inference(avatar_component_clause,[],[f5397])).

fof(f6316,plain,
    ( spl214_59
    | ~ spl214_2
    | ~ spl214_3
    | ~ spl214_8
    | ~ spl214_9
    | ~ spl214_12 ),
    inference(avatar_split_clause,[],[f5454,f5392,f5377,f5372,f5347,f5342,f6313])).

fof(f5392,plain,
    ( spl214_12
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl214_12])])).

fof(f5454,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl214_2
    | ~ spl214_3
    | ~ spl214_8
    | ~ spl214_9
    | ~ spl214_12 ),
    inference(unit_resulting_resolution,[],[f5344,f5349,f5374,f5379,f5394,f4221])).

fof(f5394,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl214_12 ),
    inference(avatar_component_clause,[],[f5392])).

fof(f5405,plain,(
    ~ spl214_14 ),
    inference(avatar_split_clause,[],[f4188,f5402])).

fof(f4188,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f3869])).

fof(f3869,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f3384,f3868,f3867,f3866,f3865,f3864])).

fof(f3864,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3865,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3866,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3867,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3868,plain,
    ( ? [X4] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3384,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3383])).

fof(f3383,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3363])).

fof(f3363,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f5400,plain,(
    spl214_13 ),
    inference(avatar_split_clause,[],[f4187,f5397])).

fof(f4187,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5395,plain,(
    spl214_12 ),
    inference(avatar_split_clause,[],[f4186,f5392])).

fof(f4186,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5390,plain,(
    spl214_11 ),
    inference(avatar_split_clause,[],[f4185,f5387])).

fof(f4185,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5385,plain,(
    spl214_10 ),
    inference(avatar_split_clause,[],[f4183,f5382])).

fof(f4183,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5380,plain,(
    spl214_9 ),
    inference(avatar_split_clause,[],[f4181,f5377])).

fof(f4181,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5375,plain,(
    spl214_8 ),
    inference(avatar_split_clause,[],[f4179,f5372])).

fof(f4179,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5370,plain,(
    ~ spl214_7 ),
    inference(avatar_split_clause,[],[f4184,f5367])).

fof(f4184,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5365,plain,(
    ~ spl214_6 ),
    inference(avatar_split_clause,[],[f4182,f5362])).

fof(f4182,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5360,plain,(
    ~ spl214_5 ),
    inference(avatar_split_clause,[],[f4180,f5357])).

fof(f4180,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5355,plain,(
    ~ spl214_4 ),
    inference(avatar_split_clause,[],[f4178,f5352])).

fof(f4178,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5350,plain,(
    spl214_3 ),
    inference(avatar_split_clause,[],[f4177,f5347])).

fof(f4177,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5345,plain,(
    spl214_2 ),
    inference(avatar_split_clause,[],[f4176,f5342])).

fof(f4176,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3869])).

fof(f5340,plain,(
    ~ spl214_1 ),
    inference(avatar_split_clause,[],[f4175,f5337])).

fof(f4175,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3869])).
%------------------------------------------------------------------------------
