%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1791+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 9.56s
% Output     : Refutation 9.56s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 340 expanded)
%              Number of leaves         :   21 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  447 (1345 expanded)
%              Number of equality atoms :   61 ( 210 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12012,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5438,f5443,f5448,f5458,f5477,f5480,f5592,f5633,f6188,f6556,f7615,f11830,f11911,f11996])).

fof(f11996,plain,
    ( spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_26
    | ~ spl209_30
    | ~ spl209_53
    | spl209_88 ),
    inference(avatar_contradiction_clause,[],[f11995])).

fof(f11995,plain,
    ( $false
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_26
    | ~ spl209_30
    | ~ spl209_53
    | spl209_88 ),
    inference(subsumption_resolution,[],[f11994,f11910])).

fof(f11910,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0)
    | spl209_88 ),
    inference(avatar_component_clause,[],[f11908])).

fof(f11908,plain,
    ( spl209_88
  <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_88])])).

fof(f11994,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_26
    | ~ spl209_30
    | ~ spl209_53 ),
    inference(forward_demodulation,[],[f11974,f11618])).

fof(f11618,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k1_xboole_0)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_26 ),
    inference(backward_demodulation,[],[f5764,f11613])).

fof(f11613,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,k1_xboole_0)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_26 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f5591,f4648,f4435])).

fof(f4435,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4036])).

fof(f4036,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3559])).

fof(f3559,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3558])).

fof(f3558,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3365])).

fof(f3365,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f4648,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f5591,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ spl209_26 ),
    inference(avatar_component_clause,[],[f5589])).

fof(f5589,plain,
    ( spl209_26
  <=> r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_26])])).

fof(f5447,plain,
    ( l1_pre_topc(sK0)
    | ~ spl209_3 ),
    inference(avatar_component_clause,[],[f5445])).

fof(f5445,plain,
    ( spl209_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_3])])).

fof(f5442,plain,
    ( v2_pre_topc(sK0)
    | ~ spl209_2 ),
    inference(avatar_component_clause,[],[f5440])).

fof(f5440,plain,
    ( spl209_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_2])])).

fof(f5437,plain,
    ( ~ v2_struct_0(sK0)
    | spl209_1 ),
    inference(avatar_component_clause,[],[f5435])).

fof(f5435,plain,
    ( spl209_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_1])])).

fof(f5764,plain,
    ( k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,k1_xboole_0))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f4648,f4284])).

fof(f4284,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3492])).

fof(f3492,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3491])).

fof(f3491,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3336])).

fof(f3336,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f11974,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_30
    | ~ spl209_53 ),
    inference(backward_demodulation,[],[f6555,f11926])).

fof(f11926,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_30 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f5457,f5631,f4435])).

fof(f5631,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl209_30 ),
    inference(avatar_component_clause,[],[f5630])).

fof(f5630,plain,
    ( spl209_30
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_30])])).

fof(f5457,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl209_5 ),
    inference(avatar_component_clause,[],[f5455])).

fof(f5455,plain,
    ( spl209_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_5])])).

fof(f6555,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl209_53 ),
    inference(avatar_component_clause,[],[f6553])).

fof(f6553,plain,
    ( spl209_53
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_53])])).

fof(f11911,plain,
    ( ~ spl209_88
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | spl209_9
    | ~ spl209_26 ),
    inference(avatar_split_clause,[],[f11906,f5589,f5474,f5445,f5440,f5435,f11908])).

fof(f5474,plain,
    ( spl209_9
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_9])])).

fof(f11906,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | spl209_9
    | ~ spl209_26 ),
    inference(forward_demodulation,[],[f5475,f11618])).

fof(f5475,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | spl209_9 ),
    inference(avatar_component_clause,[],[f5474])).

fof(f11830,plain,
    ( spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_9
    | ~ spl209_26
    | spl209_30
    | ~ spl209_48 ),
    inference(avatar_contradiction_clause,[],[f11829])).

fof(f11829,plain,
    ( $false
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_9
    | ~ spl209_26
    | spl209_30
    | ~ spl209_48 ),
    inference(subsumption_resolution,[],[f11811,f5632])).

fof(f5632,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl209_30 ),
    inference(avatar_component_clause,[],[f5630])).

fof(f11811,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_9
    | ~ spl209_26
    | ~ spl209_48 ),
    inference(backward_demodulation,[],[f10509,f11807])).

fof(f11807,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_9
    | ~ spl209_26
    | ~ spl209_48 ),
    inference(forward_demodulation,[],[f11676,f11617])).

fof(f11617,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_26 ),
    inference(backward_demodulation,[],[f5761,f11613])).

fof(f5761,plain,
    ( k5_tmap_1(sK0,k1_xboole_0) = u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f4648,f4283])).

fof(f4283,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3490])).

fof(f3490,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3489])).

fof(f3489,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3366])).

fof(f3366,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f11676,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_9
    | ~ spl209_26
    | ~ spl209_48 ),
    inference(backward_demodulation,[],[f6187,f11619])).

fof(f11619,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0)
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_9
    | ~ spl209_26 ),
    inference(backward_demodulation,[],[f5476,f11618])).

fof(f5476,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl209_9 ),
    inference(avatar_component_clause,[],[f5474])).

fof(f6187,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl209_48 ),
    inference(avatar_component_clause,[],[f6185])).

fof(f6185,plain,
    ( spl209_48
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_48])])).

fof(f10509,plain,
    ( r2_hidden(sK1,k5_tmap_1(sK0,sK1))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f5457,f4438])).

fof(f4438,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3563])).

fof(f3563,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3562])).

fof(f3562,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

fof(f7615,plain,
    ( ~ spl209_3
    | ~ spl209_5
    | ~ spl209_8
    | spl209_30 ),
    inference(avatar_contradiction_clause,[],[f7614])).

fof(f7614,plain,
    ( $false
    | ~ spl209_3
    | ~ spl209_5
    | ~ spl209_8
    | spl209_30 ),
    inference(subsumption_resolution,[],[f5472,f5634])).

fof(f5634,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl209_3
    | ~ spl209_5
    | spl209_30 ),
    inference(unit_resulting_resolution,[],[f5447,f5457,f5632,f4371])).

fof(f4371,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f4001])).

fof(f4001,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3522])).

fof(f3522,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f5472,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl209_8 ),
    inference(avatar_component_clause,[],[f5470])).

fof(f5470,plain,
    ( spl209_8
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl209_8])])).

fof(f6556,plain,
    ( spl209_53
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5 ),
    inference(avatar_split_clause,[],[f5551,f5455,f5445,f5440,f5435,f6553])).

fof(f5551,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f5457,f4284])).

fof(f6188,plain,
    ( spl209_48
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5 ),
    inference(avatar_split_clause,[],[f5544,f5455,f5445,f5440,f5435,f6185])).

fof(f5544,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl209_1
    | ~ spl209_2
    | ~ spl209_3
    | ~ spl209_5 ),
    inference(unit_resulting_resolution,[],[f5437,f5442,f5447,f5457,f4283])).

fof(f5633,plain,
    ( ~ spl209_30
    | ~ spl209_3
    | ~ spl209_5
    | spl209_8 ),
    inference(avatar_split_clause,[],[f5522,f5470,f5455,f5445,f5630])).

fof(f5522,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl209_3
    | ~ spl209_5
    | spl209_8 ),
    inference(unit_resulting_resolution,[],[f5447,f5471,f5457,f4372])).

fof(f4372,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4001])).

fof(f5471,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl209_8 ),
    inference(avatar_component_clause,[],[f5470])).

fof(f5592,plain,
    ( spl209_26
    | ~ spl209_2
    | ~ spl209_3 ),
    inference(avatar_split_clause,[],[f5492,f5445,f5440,f5589])).

fof(f5492,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ spl209_2
    | ~ spl209_3 ),
    inference(unit_resulting_resolution,[],[f5442,f5447,f4369])).

fof(f4369,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3519])).

fof(f3519,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3518])).

fof(f3518,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1851])).

fof(f1851,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f5480,plain,
    ( ~ spl209_8
    | ~ spl209_9 ),
    inference(avatar_split_clause,[],[f5479,f5474,f5470])).

fof(f5479,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl209_9 ),
    inference(trivial_inequality_removal,[],[f5478])).

fof(f5478,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl209_9 ),
    inference(backward_demodulation,[],[f4274,f5476])).

fof(f4274,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3977])).

fof(f3977,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3974,f3976,f3975])).

fof(f3975,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3976,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3974,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3973])).

fof(f3973,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3482])).

fof(f3482,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3481])).

fof(f3481,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3369])).

fof(f3369,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3368])).

fof(f3368,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f5477,plain,
    ( spl209_8
    | spl209_9 ),
    inference(avatar_split_clause,[],[f4273,f5474,f5470])).

fof(f4273,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3977])).

fof(f5458,plain,(
    spl209_5 ),
    inference(avatar_split_clause,[],[f4272,f5455])).

fof(f4272,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3977])).

fof(f5448,plain,(
    spl209_3 ),
    inference(avatar_split_clause,[],[f4271,f5445])).

fof(f4271,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3977])).

fof(f5443,plain,(
    spl209_2 ),
    inference(avatar_split_clause,[],[f4270,f5440])).

fof(f4270,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3977])).

fof(f5438,plain,(
    ~ spl209_1 ),
    inference(avatar_split_clause,[],[f4269,f5435])).

fof(f4269,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3977])).
%------------------------------------------------------------------------------
