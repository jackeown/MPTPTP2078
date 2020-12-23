%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1714+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 15.81s
% Output     : Refutation 16.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 260 expanded)
%              Number of leaves         :   30 ( 124 expanded)
%              Depth                    :    7
%              Number of atoms          :  440 (1686 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5733,f5742,f5747,f5752,f5762,f5772,f5782,f5787,f6388,f6865,f7064,f7314,f7337,f13343,f14072,f14352,f14440,f14568,f14609,f27365])).

fof(f27365,plain,
    ( ~ spl309_244
    | spl309_825
    | ~ spl309_844 ),
    inference(avatar_contradiction_clause,[],[f27364])).

fof(f27364,plain,
    ( $false
    | ~ spl309_244
    | spl309_825
    | ~ spl309_844 ),
    inference(subsumption_resolution,[],[f27277,f14608])).

fof(f14608,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl309_844 ),
    inference(avatar_component_clause,[],[f14606])).

fof(f14606,plain,
    ( spl309_844
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_844])])).

fof(f27277,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl309_244
    | spl309_825 ),
    inference(unit_resulting_resolution,[],[f7336,f14439,f4332])).

fof(f4332,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3443])).

fof(f3443,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f3442])).

fof(f3442,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f14439,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl309_825 ),
    inference(avatar_component_clause,[],[f14437])).

fof(f14437,plain,
    ( spl309_825
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_825])])).

fof(f7336,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl309_244 ),
    inference(avatar_component_clause,[],[f7334])).

fof(f7334,plain,
    ( spl309_244
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_244])])).

fof(f14609,plain,
    ( spl309_844
    | ~ spl309_1
    | ~ spl309_111
    | ~ spl309_794 ),
    inference(avatar_split_clause,[],[f14598,f13915,f6385,f5726,f14606])).

fof(f5726,plain,
    ( spl309_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_1])])).

fof(f6385,plain,
    ( spl309_111
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_111])])).

fof(f13915,plain,
    ( spl309_794
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_794])])).

fof(f14598,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl309_1
    | ~ spl309_111
    | ~ spl309_794 ),
    inference(unit_resulting_resolution,[],[f13916,f6386,f5728,f4268])).

fof(f4268,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3882])).

fof(f3882,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3382])).

fof(f3382,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3327])).

fof(f3327,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f5728,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl309_1 ),
    inference(avatar_component_clause,[],[f5726])).

fof(f6386,plain,
    ( l1_struct_0(sK3)
    | ~ spl309_111 ),
    inference(avatar_component_clause,[],[f6385])).

fof(f13916,plain,
    ( l1_struct_0(sK2)
    | ~ spl309_794 ),
    inference(avatar_component_clause,[],[f13915])).

fof(f14568,plain,
    ( spl309_1
    | ~ spl309_2
    | ~ spl309_111
    | ~ spl309_794 ),
    inference(avatar_split_clause,[],[f14475,f13915,f6385,f5730,f5726])).

fof(f5730,plain,
    ( spl309_2
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_2])])).

fof(f14475,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl309_2
    | ~ spl309_111
    | ~ spl309_794 ),
    inference(unit_resulting_resolution,[],[f6386,f5732,f13916,f4265])).

fof(f4265,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3379])).

fof(f3379,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f3378])).

fof(f3378,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3339])).

fof(f3339,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f5732,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl309_2 ),
    inference(avatar_component_clause,[],[f5730])).

fof(f14440,plain,
    ( ~ spl309_825
    | spl309_3
    | ~ spl309_110
    | ~ spl309_111 ),
    inference(avatar_split_clause,[],[f14355,f6385,f6381,f5735,f14437])).

fof(f5735,plain,
    ( spl309_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_3])])).

fof(f6381,plain,
    ( spl309_110
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_110])])).

fof(f14355,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl309_3
    | ~ spl309_110
    | ~ spl309_111 ),
    inference(unit_resulting_resolution,[],[f6386,f5737,f6382,f4269])).

fof(f4269,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3882])).

fof(f6382,plain,
    ( l1_struct_0(sK1)
    | ~ spl309_110 ),
    inference(avatar_component_clause,[],[f6381])).

fof(f5737,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl309_3 ),
    inference(avatar_component_clause,[],[f5735])).

fof(f14352,plain,
    ( ~ spl309_38
    | spl309_110 ),
    inference(avatar_contradiction_clause,[],[f14351])).

fof(f14351,plain,
    ( $false
    | ~ spl309_38
    | spl309_110 ),
    inference(subsumption_resolution,[],[f14343,f5931])).

fof(f5931,plain,
    ( l1_pre_topc(sK1)
    | ~ spl309_38 ),
    inference(avatar_component_clause,[],[f5930])).

fof(f5930,plain,
    ( spl309_38
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_38])])).

fof(f14343,plain,
    ( ~ l1_pre_topc(sK1)
    | spl309_110 ),
    inference(resolution,[],[f6383,f4308])).

fof(f4308,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3416])).

fof(f3416,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f6383,plain,
    ( ~ l1_struct_0(sK1)
    | spl309_110 ),
    inference(avatar_component_clause,[],[f6381])).

fof(f14072,plain,
    ( ~ spl309_27
    | spl309_794 ),
    inference(avatar_contradiction_clause,[],[f14071])).

fof(f14071,plain,
    ( $false
    | ~ spl309_27
    | spl309_794 ),
    inference(subsumption_resolution,[],[f14063,f5872])).

fof(f5872,plain,
    ( l1_pre_topc(sK2)
    | ~ spl309_27 ),
    inference(avatar_component_clause,[],[f5871])).

fof(f5871,plain,
    ( spl309_27
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_27])])).

fof(f14063,plain,
    ( ~ l1_pre_topc(sK2)
    | spl309_794 ),
    inference(resolution,[],[f13917,f4308])).

fof(f13917,plain,
    ( ~ l1_struct_0(sK2)
    | spl309_794 ),
    inference(avatar_component_clause,[],[f13915])).

fof(f13343,plain,
    ( spl309_111
    | ~ spl309_16 ),
    inference(avatar_split_clause,[],[f13097,f5812,f6385])).

fof(f5812,plain,
    ( spl309_16
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_16])])).

fof(f13097,plain,
    ( l1_struct_0(sK3)
    | ~ spl309_16 ),
    inference(unit_resulting_resolution,[],[f5813,f4308])).

fof(f5813,plain,
    ( l1_pre_topc(sK3)
    | ~ spl309_16 ),
    inference(avatar_component_clause,[],[f5812])).

fof(f7337,plain,
    ( spl309_244
    | ~ spl309_5
    | ~ spl309_8
    | ~ spl309_10
    | ~ spl309_12
    | ~ spl309_13 ),
    inference(avatar_split_clause,[],[f7138,f5784,f5779,f5769,f5759,f5744,f7334])).

fof(f5744,plain,
    ( spl309_5
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_5])])).

fof(f5759,plain,
    ( spl309_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_8])])).

fof(f5769,plain,
    ( spl309_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_10])])).

fof(f5779,plain,
    ( spl309_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_12])])).

fof(f5784,plain,
    ( spl309_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_13])])).

fof(f7138,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl309_5
    | ~ spl309_8
    | ~ spl309_10
    | ~ spl309_12
    | ~ spl309_13 ),
    inference(unit_resulting_resolution,[],[f5786,f5781,f5746,f5761,f5771,f4277])).

fof(f4277,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3888])).

fof(f3888,plain,(
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
    inference(nnf_transformation,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3385])).

fof(f3385,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3360])).

fof(f3360,axiom,(
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

fof(f5771,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl309_10 ),
    inference(avatar_component_clause,[],[f5769])).

fof(f5761,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl309_8 ),
    inference(avatar_component_clause,[],[f5759])).

fof(f5746,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl309_5 ),
    inference(avatar_component_clause,[],[f5744])).

fof(f5781,plain,
    ( l1_pre_topc(sK0)
    | ~ spl309_12 ),
    inference(avatar_component_clause,[],[f5779])).

fof(f5786,plain,
    ( v2_pre_topc(sK0)
    | ~ spl309_13 ),
    inference(avatar_component_clause,[],[f5784])).

fof(f7314,plain,
    ( spl309_38
    | ~ spl309_10
    | ~ spl309_12 ),
    inference(avatar_split_clause,[],[f7149,f5779,f5769,f5930])).

fof(f7149,plain,
    ( l1_pre_topc(sK1)
    | ~ spl309_10
    | ~ spl309_12 ),
    inference(unit_resulting_resolution,[],[f5781,f5771,f4296])).

fof(f4296,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3403])).

fof(f3403,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f7064,plain,
    ( spl309_27
    | ~ spl309_8
    | ~ spl309_12 ),
    inference(avatar_split_clause,[],[f6923,f5779,f5759,f5871])).

fof(f6923,plain,
    ( l1_pre_topc(sK2)
    | ~ spl309_8
    | ~ spl309_12 ),
    inference(unit_resulting_resolution,[],[f5781,f5761,f4296])).

fof(f6865,plain,
    ( spl309_16
    | ~ spl309_6
    | ~ spl309_12 ),
    inference(avatar_split_clause,[],[f6688,f5779,f5749,f5812])).

fof(f5749,plain,
    ( spl309_6
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_6])])).

fof(f6688,plain,
    ( l1_pre_topc(sK3)
    | ~ spl309_6
    | ~ spl309_12 ),
    inference(unit_resulting_resolution,[],[f5781,f5751,f4296])).

fof(f5751,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl309_6 ),
    inference(avatar_component_clause,[],[f5749])).

fof(f6388,plain,
    ( ~ spl309_110
    | ~ spl309_111
    | ~ spl309_3
    | spl309_4 ),
    inference(avatar_split_clause,[],[f6379,f5739,f5735,f6385,f6381])).

fof(f5739,plain,
    ( spl309_4
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl309_4])])).

fof(f6379,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | spl309_4 ),
    inference(resolution,[],[f5741,f4265])).

fof(f5741,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl309_4 ),
    inference(avatar_component_clause,[],[f5739])).

fof(f5787,plain,(
    spl309_13 ),
    inference(avatar_split_clause,[],[f4254,f5784])).

fof(f4254,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3881])).

fof(f3881,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3377,f3880,f3879,f3878,f3877])).

fof(f3877,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
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

fof(f3878,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3879,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3880,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3377,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3376])).

fof(f3376,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3359])).

fof(f3359,negated_conjecture,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3358])).

fof(f3358,conjecture,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f5782,plain,(
    spl309_12 ),
    inference(avatar_split_clause,[],[f4255,f5779])).

fof(f4255,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5772,plain,(
    spl309_10 ),
    inference(avatar_split_clause,[],[f4257,f5769])).

fof(f4257,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5762,plain,(
    spl309_8 ),
    inference(avatar_split_clause,[],[f4259,f5759])).

fof(f4259,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5752,plain,(
    spl309_6 ),
    inference(avatar_split_clause,[],[f4261,f5749])).

fof(f4261,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5747,plain,(
    spl309_5 ),
    inference(avatar_split_clause,[],[f4262,f5744])).

fof(f4262,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5742,plain,
    ( ~ spl309_3
    | ~ spl309_4 ),
    inference(avatar_split_clause,[],[f4263,f5739,f5735])).

fof(f4263,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3881])).

fof(f5733,plain,
    ( spl309_1
    | spl309_2 ),
    inference(avatar_split_clause,[],[f4264,f5730,f5726])).

fof(f4264,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f3881])).
%------------------------------------------------------------------------------
