%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:18 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 408 expanded)
%              Number of leaves         :   24 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          :  443 (1246 expanded)
%              Number of equality atoms :   81 ( 308 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f364,f374,f383,f392,f1311,f1437,f1892,f2242])).

fof(f2242,plain,
    ( ~ spl19_1
    | ~ spl19_3
    | spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(avatar_contradiction_clause,[],[f2241])).

fof(f2241,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_3
    | spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f2240,f377])).

fof(f377,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl19_4 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl19_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f2240,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(forward_demodulation,[],[f2239,f1346])).

fof(f1346,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | ~ spl19_3
    | ~ spl19_34 ),
    inference(forward_demodulation,[],[f1345,f562])).

fof(f562,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_3 ),
    inference(forward_demodulation,[],[f552,f541])).

fof(f541,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl19_3 ),
    inference(unit_resulting_resolution,[],[f373,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f373,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl19_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f552,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_3 ),
    inference(unit_resulting_resolution,[],[f373,f305])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1345,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | ~ spl19_3
    | ~ spl19_34 ),
    inference(forward_demodulation,[],[f1321,f707])).

fof(f707,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))
    | ~ spl19_3 ),
    inference(unit_resulting_resolution,[],[f373,f344])).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f336,f289])).

fof(f289,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1321,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_34 ),
    inference(unit_resulting_resolution,[],[f1310,f304])).

fof(f1310,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_34 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1308,plain,
    ( spl19_34
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_34])])).

fof(f2239,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f2238,f1310])).

fof(f2238,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f2236,f1944])).

fof(f1944,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_30
    | ~ spl19_34 ),
    inference(unit_resulting_resolution,[],[f363,f382,f1310,f1194,f260])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1194,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_30 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1193,plain,
    ( spl19_30
  <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_30])])).

fof(f382,plain,
    ( v2_pre_topc(sK0)
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl19_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f363,plain,
    ( l1_pre_topc(sK0)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl19_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2236,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(superposition,[],[f1171,f707])).

fof(f1171,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f776,f1107])).

fof(f1107,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f415,f337])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f415,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f352,f330])).

fof(f330,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f352,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f776,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f773,f762])).

fof(f762,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f761,f664])).

fof(f664,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_3 ),
    inference(forward_demodulation,[],[f654,f541])).

fof(f654,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_3 ),
    inference(unit_resulting_resolution,[],[f373,f356])).

fof(f356,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f307,f214])).

fof(f214,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f307,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f761,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f757,f541])).

fof(f757,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(unit_resulting_resolution,[],[f391,f373,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f391,plain,
    ( l1_struct_0(sK0)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl19_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f773,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl19_1 ),
    inference(resolution,[],[f263,f363])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f1892,plain,
    ( ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f1890,f378])).

fof(f378,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f376])).

fof(f1890,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f1375,f1886])).

fof(f1886,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f1719,f1885])).

fof(f1885,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f1884,f378])).

fof(f1884,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(forward_demodulation,[],[f1859,f1346])).

fof(f1859,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6
    | ~ spl19_34 ),
    inference(subsumption_resolution,[],[f1858,f1310])).

fof(f1858,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(superposition,[],[f1170,f707])).

fof(f1170,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f780,f1107])).

fof(f780,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl19_1
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f777,f762])).

fof(f777,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl19_1 ),
    inference(resolution,[],[f264,f363])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f1719,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl19_1
    | ~ spl19_34 ),
    inference(resolution,[],[f718,f1310])).

fof(f718,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl19_1 ),
    inference(resolution,[],[f259,f363])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f1375,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f1374,f1107])).

fof(f1374,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f213,f762])).

fof(f213,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,
    ( ( ( ~ v3_pre_topc(sK1,sK0)
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v2_pre_topc(sK0) )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v3_pre_topc(sK1,sK0) ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f71,f153,f152])).

fof(f152,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v3_pre_topc(X1,X0)
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v3_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,sK0)
              & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v2_pre_topc(sK0) )
            | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v3_pre_topc(X1,sK0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f153,plain,
    ( ? [X1] :
        ( ( ( ~ v3_pre_topc(X1,sK0)
            & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
            & v2_pre_topc(sK0) )
          | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
            & v3_pre_topc(X1,sK0) ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( ~ v3_pre_topc(sK1,sK0)
          & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
          & v2_pre_topc(sK0) )
        | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
          & v3_pre_topc(sK1,sK0) ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f67])).

fof(f67,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f1437,plain,
    ( spl19_4
    | ~ spl19_3
    | ~ spl19_6
    | spl19_30 ),
    inference(avatar_split_clause,[],[f1377,f1193,f389,f371,f376])).

fof(f1377,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl19_3
    | ~ spl19_6
    | spl19_30 ),
    inference(subsumption_resolution,[],[f1376,f1195])).

fof(f1195,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | spl19_30 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1376,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f989,f1107])).

fof(f989,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f210,f762])).

fof(f210,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f154])).

fof(f1311,plain,
    ( spl19_34
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f551,f371,f1308])).

fof(f551,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_3 ),
    inference(backward_demodulation,[],[f479,f541])).

fof(f479,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_3 ),
    inference(unit_resulting_resolution,[],[f373,f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f392,plain,
    ( spl19_6
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f384,f361,f389])).

fof(f384,plain,
    ( l1_struct_0(sK0)
    | ~ spl19_1 ),
    inference(unit_resulting_resolution,[],[f363,f226])).

fof(f226,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f383,plain,
    ( spl19_4
    | spl19_5 ),
    inference(avatar_split_clause,[],[f208,f380,f376])).

fof(f208,plain,
    ( v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f154])).

fof(f374,plain,(
    spl19_3 ),
    inference(avatar_split_clause,[],[f207,f371])).

fof(f207,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f154])).

fof(f364,plain,(
    spl19_1 ),
    inference(avatar_split_clause,[],[f206,f361])).

fof(f206,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (14248)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (14272)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (14267)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (14265)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (14250)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.52  % (14243)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.52  % (14264)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.53  % (14255)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.53  % (14247)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.53  % (14269)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.53  % (14260)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.53  % (14244)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.54  % (14245)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.54  % (14246)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.54  % (14249)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (14261)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.55  % (14266)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.55  % (14253)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.55  % (14252)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % (14261)Refutation not found, incomplete strategy% (14261)------------------------------
% 1.40/0.55  % (14261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14261)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14261)Memory used [KB]: 10874
% 1.40/0.55  % (14261)Time elapsed: 0.139 s
% 1.40/0.55  % (14261)------------------------------
% 1.40/0.55  % (14261)------------------------------
% 1.40/0.55  % (14258)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.55  % (14270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.56  % (14262)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.56  % (14259)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.56  % (14271)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (14268)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.56  % (14274)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.57  % (14254)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.57  % (14263)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.57  % (14257)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.58  % (14273)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.59  % (14254)Refutation not found, incomplete strategy% (14254)------------------------------
% 1.40/0.59  % (14254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (14254)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.59  
% 1.40/0.59  % (14254)Memory used [KB]: 11129
% 1.40/0.59  % (14254)Time elapsed: 0.190 s
% 1.40/0.59  % (14254)------------------------------
% 1.40/0.59  % (14254)------------------------------
% 2.02/0.63  % (14273)Refutation not found, incomplete strategy% (14273)------------------------------
% 2.02/0.63  % (14273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.65  % (14273)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.65  
% 2.02/0.65  % (14273)Memory used [KB]: 11257
% 2.02/0.65  % (14273)Time elapsed: 0.232 s
% 2.02/0.65  % (14273)------------------------------
% 2.02/0.65  % (14273)------------------------------
% 2.02/0.68  % (14265)Refutation found. Thanks to Tanya!
% 2.02/0.68  % SZS status Theorem for theBenchmark
% 2.02/0.68  % SZS output start Proof for theBenchmark
% 2.02/0.68  fof(f2243,plain,(
% 2.02/0.68    $false),
% 2.02/0.68    inference(avatar_sat_refutation,[],[f364,f374,f383,f392,f1311,f1437,f1892,f2242])).
% 2.02/0.68  fof(f2242,plain,(
% 2.02/0.68    ~spl19_1 | ~spl19_3 | spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_30 | ~spl19_34),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f2241])).
% 2.02/0.68  fof(f2241,plain,(
% 2.02/0.68    $false | (~spl19_1 | ~spl19_3 | spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_30 | ~spl19_34)),
% 2.02/0.68    inference(subsumption_resolution,[],[f2240,f377])).
% 2.02/0.68  fof(f377,plain,(
% 2.02/0.68    ~v3_pre_topc(sK1,sK0) | spl19_4),
% 2.02/0.68    inference(avatar_component_clause,[],[f376])).
% 2.02/0.68  fof(f376,plain,(
% 2.02/0.68    spl19_4 <=> v3_pre_topc(sK1,sK0)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).
% 2.02/0.68  fof(f2240,plain,(
% 2.02/0.68    v3_pre_topc(sK1,sK0) | (~spl19_1 | ~spl19_3 | ~spl19_5 | ~spl19_6 | ~spl19_30 | ~spl19_34)),
% 2.02/0.68    inference(forward_demodulation,[],[f2239,f1346])).
% 2.02/0.68  fof(f1346,plain,(
% 2.02/0.68    sK1 = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | (~spl19_3 | ~spl19_34)),
% 2.02/0.68    inference(forward_demodulation,[],[f1345,f562])).
% 2.02/0.68  fof(f562,plain,(
% 2.02/0.68    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl19_3),
% 2.02/0.68    inference(forward_demodulation,[],[f552,f541])).
% 2.02/0.68  fof(f541,plain,(
% 2.02/0.68    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl19_3),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f373,f304])).
% 2.02/0.68  fof(f304,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f125])).
% 2.02/0.68  fof(f125,plain,(
% 2.02/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f13])).
% 2.02/0.68  fof(f13,axiom,(
% 2.02/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.02/0.68  fof(f373,plain,(
% 2.02/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl19_3),
% 2.02/0.68    inference(avatar_component_clause,[],[f371])).
% 2.02/0.68  fof(f371,plain,(
% 2.02/0.68    spl19_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).
% 2.02/0.68  fof(f552,plain,(
% 2.02/0.68    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl19_3),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f373,f305])).
% 2.02/0.68  fof(f305,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.02/0.68    inference(cnf_transformation,[],[f126])).
% 2.02/0.68  fof(f126,plain,(
% 2.02/0.68    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f17])).
% 2.02/0.68  fof(f17,axiom,(
% 2.02/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.02/0.68  fof(f1345,plain,(
% 2.02/0.68    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | (~spl19_3 | ~spl19_34)),
% 2.02/0.68    inference(forward_demodulation,[],[f1321,f707])).
% 2.02/0.68  fof(f707,plain,(
% 2.02/0.68    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))) ) | ~spl19_3),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f373,f344])).
% 2.02/0.68  fof(f344,plain,(
% 2.02/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.02/0.68    inference(definition_unfolding,[],[f336,f289])).
% 2.02/0.68  fof(f289,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f4])).
% 2.02/0.68  fof(f4,axiom,(
% 2.02/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.02/0.68  fof(f336,plain,(
% 2.02/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f145])).
% 2.02/0.68  fof(f145,plain,(
% 2.02/0.68    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f20])).
% 2.02/0.68  fof(f20,axiom,(
% 2.02/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.02/0.68  fof(f1321,plain,(
% 2.02/0.68    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl19_34),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f1310,f304])).
% 2.02/0.68  fof(f1310,plain,(
% 2.02/0.68    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl19_34),
% 2.02/0.68    inference(avatar_component_clause,[],[f1308])).
% 2.02/0.68  fof(f1308,plain,(
% 2.02/0.68    spl19_34 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_34])])).
% 2.02/0.68  fof(f2239,plain,(
% 2.02/0.68    v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_3 | ~spl19_5 | ~spl19_6 | ~spl19_30 | ~spl19_34)),
% 2.02/0.68    inference(subsumption_resolution,[],[f2238,f1310])).
% 2.02/0.68  fof(f2238,plain,(
% 2.02/0.68    v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl19_1 | ~spl19_3 | ~spl19_5 | ~spl19_6 | ~spl19_30 | ~spl19_34)),
% 2.02/0.68    inference(subsumption_resolution,[],[f2236,f1944])).
% 2.02/0.68  fof(f1944,plain,(
% 2.02/0.68    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_5 | ~spl19_30 | ~spl19_34)),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f363,f382,f1310,f1194,f260])).
% 2.02/0.68  fof(f260,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f90])).
% 2.02/0.68  fof(f90,plain,(
% 2.02/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.68    inference(flattening,[],[f89])).
% 2.02/0.68  fof(f89,plain,(
% 2.02/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.68    inference(ennf_transformation,[],[f65])).
% 2.02/0.68  fof(f65,axiom,(
% 2.02/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.02/0.68  fof(f1194,plain,(
% 2.02/0.68    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl19_30),
% 2.02/0.68    inference(avatar_component_clause,[],[f1193])).
% 2.02/0.68  fof(f1193,plain,(
% 2.02/0.68    spl19_30 <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_30])])).
% 2.02/0.68  fof(f382,plain,(
% 2.02/0.68    v2_pre_topc(sK0) | ~spl19_5),
% 2.02/0.68    inference(avatar_component_clause,[],[f380])).
% 2.02/0.68  fof(f380,plain,(
% 2.02/0.68    spl19_5 <=> v2_pre_topc(sK0)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).
% 2.02/0.68  fof(f363,plain,(
% 2.02/0.68    l1_pre_topc(sK0) | ~spl19_1),
% 2.02/0.68    inference(avatar_component_clause,[],[f361])).
% 2.02/0.68  fof(f361,plain,(
% 2.02/0.68    spl19_1 <=> l1_pre_topc(sK0)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).
% 2.02/0.68  fof(f2236,plain,(
% 2.02/0.68    v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.02/0.68    inference(superposition,[],[f1171,f707])).
% 2.02/0.68  fof(f1171,plain,(
% 2.02/0.68    ( ! [X0] : (v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.02/0.68    inference(backward_demodulation,[],[f776,f1107])).
% 2.02/0.68  fof(f1107,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f415,f337])).
% 2.02/0.68  fof(f337,plain,(
% 2.02/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f146])).
% 2.02/0.68  fof(f146,plain,(
% 2.02/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f19])).
% 2.02/0.68  fof(f19,axiom,(
% 2.02/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.02/0.68  fof(f415,plain,(
% 2.02/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f352,f330])).
% 2.02/0.68  fof(f330,plain,(
% 2.02/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f203])).
% 2.02/0.68  fof(f203,plain,(
% 2.02/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.02/0.68    inference(nnf_transformation,[],[f29])).
% 2.02/0.68  fof(f29,axiom,(
% 2.02/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.02/0.68  fof(f352,plain,(
% 2.02/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.68    inference(equality_resolution,[],[f323])).
% 2.02/0.68  fof(f323,plain,(
% 2.02/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.02/0.68    inference(cnf_transformation,[],[f200])).
% 2.02/0.68  fof(f200,plain,(
% 2.02/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.68    inference(flattening,[],[f199])).
% 2.02/0.68  fof(f199,plain,(
% 2.02/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.68    inference(nnf_transformation,[],[f2])).
% 2.02/0.68  fof(f2,axiom,(
% 2.02/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.68  fof(f776,plain,(
% 2.02/0.68    ( ! [X0] : (v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.02/0.68    inference(forward_demodulation,[],[f773,f762])).
% 2.46/0.68  fof(f762,plain,(
% 2.46/0.68    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f761,f664])).
% 2.46/0.68  fof(f664,plain,(
% 2.46/0.68    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl19_3),
% 2.46/0.68    inference(forward_demodulation,[],[f654,f541])).
% 2.46/0.68  fof(f654,plain,(
% 2.46/0.68    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl19_3),
% 2.46/0.68    inference(unit_resulting_resolution,[],[f373,f356])).
% 2.46/0.68  fof(f356,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 2.46/0.68    inference(forward_demodulation,[],[f307,f214])).
% 2.46/0.68  fof(f214,plain,(
% 2.46/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.46/0.68    inference(cnf_transformation,[],[f12])).
% 2.46/0.68  fof(f12,axiom,(
% 2.46/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.46/0.68  fof(f307,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.46/0.68    inference(cnf_transformation,[],[f128])).
% 2.46/0.68  fof(f128,plain,(
% 2.46/0.68    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.46/0.68    inference(ennf_transformation,[],[f22])).
% 2.46/0.68  fof(f22,axiom,(
% 2.46/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.46/0.68  fof(f761,plain,(
% 2.46/0.68    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f757,f541])).
% 2.46/0.68  fof(f757,plain,(
% 2.46/0.68    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(unit_resulting_resolution,[],[f391,f373,f221])).
% 2.46/0.68  fof(f221,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))) )),
% 2.46/0.68    inference(cnf_transformation,[],[f75])).
% 2.46/0.68  fof(f75,plain,(
% 2.46/0.68    ! [X0] : (! [X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.46/0.68    inference(ennf_transformation,[],[f60])).
% 2.46/0.68  fof(f60,axiom,(
% 2.46/0.68    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).
% 2.46/0.68  fof(f391,plain,(
% 2.46/0.68    l1_struct_0(sK0) | ~spl19_6),
% 2.46/0.68    inference(avatar_component_clause,[],[f389])).
% 2.46/0.68  fof(f389,plain,(
% 2.46/0.68    spl19_6 <=> l1_struct_0(sK0)),
% 2.46/0.68    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).
% 2.46/0.68  fof(f773,plain,(
% 2.46/0.68    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)) ) | ~spl19_1),
% 2.46/0.68    inference(resolution,[],[f263,f363])).
% 2.46/0.68  fof(f263,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f172])).
% 2.46/0.68  fof(f172,plain,(
% 2.46/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/0.68    inference(nnf_transformation,[],[f92])).
% 2.46/0.68  fof(f92,plain,(
% 2.46/0.68    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/0.68    inference(ennf_transformation,[],[f43])).
% 2.46/0.68  fof(f43,axiom,(
% 2.46/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 2.46/0.68  fof(f1892,plain,(
% 2.46/0.68    ~spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_6 | ~spl19_34),
% 2.46/0.68    inference(avatar_contradiction_clause,[],[f1891])).
% 2.46/0.68  fof(f1891,plain,(
% 2.46/0.68    $false | (~spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1890,f378])).
% 2.46/0.68  fof(f378,plain,(
% 2.46/0.68    v3_pre_topc(sK1,sK0) | ~spl19_4),
% 2.46/0.68    inference(avatar_component_clause,[],[f376])).
% 2.46/0.68  fof(f1890,plain,(
% 2.46/0.68    ~v3_pre_topc(sK1,sK0) | (~spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1375,f1886])).
% 2.46/0.68  fof(f1886,plain,(
% 2.46/0.68    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1719,f1885])).
% 2.46/0.68  fof(f1885,plain,(
% 2.46/0.68    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1884,f378])).
% 2.46/0.68  fof(f1884,plain,(
% 2.46/0.68    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_3 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(forward_demodulation,[],[f1859,f1346])).
% 2.46/0.68  fof(f1859,plain,(
% 2.46/0.68    ~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_3 | ~spl19_6 | ~spl19_34)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1858,f1310])).
% 2.46/0.68  fof(f1858,plain,(
% 2.46/0.68    ~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(superposition,[],[f1170,f707])).
% 2.46/0.68  fof(f1170,plain,(
% 2.46/0.68    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(backward_demodulation,[],[f780,f1107])).
% 2.46/0.68  fof(f780,plain,(
% 2.46/0.68    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl19_1 | ~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f777,f762])).
% 2.46/0.68  fof(f777,plain,(
% 2.46/0.68    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl19_1),
% 2.46/0.68    inference(resolution,[],[f264,f363])).
% 2.46/0.68  fof(f264,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f172])).
% 2.46/0.68  fof(f1719,plain,(
% 2.46/0.68    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl19_1 | ~spl19_34)),
% 2.46/0.68    inference(resolution,[],[f718,f1310])).
% 2.46/0.68  fof(f718,plain,(
% 2.46/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl19_1),
% 2.46/0.68    inference(resolution,[],[f259,f363])).
% 2.46/0.68  fof(f259,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 2.46/0.68    inference(cnf_transformation,[],[f90])).
% 2.46/0.68  fof(f1375,plain,(
% 2.46/0.68    k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f1374,f1107])).
% 2.46/0.68  fof(f1374,plain,(
% 2.46/0.68    k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f213,f762])).
% 2.46/0.68  fof(f213,plain,(
% 2.46/0.68    ~v3_pre_topc(sK1,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 2.46/0.68    inference(cnf_transformation,[],[f154])).
% 2.46/0.68  fof(f154,plain,(
% 2.46/0.68    (((~v3_pre_topc(sK1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v3_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.46/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f71,f153,f152])).
% 2.46/0.68  fof(f152,plain,(
% 2.46/0.68    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v3_pre_topc(X1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v3_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.46/0.68    introduced(choice_axiom,[])).
% 2.46/0.68  fof(f153,plain,(
% 2.46/0.68    ? [X1] : (((~v3_pre_topc(X1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v3_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (((~v3_pre_topc(sK1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v3_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.46/0.68    introduced(choice_axiom,[])).
% 2.46/0.68  fof(f71,plain,(
% 2.46/0.68    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.46/0.68    inference(flattening,[],[f70])).
% 2.46/0.68  fof(f70,plain,(
% 2.46/0.68    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.46/0.68    inference(ennf_transformation,[],[f68])).
% 2.46/0.68  fof(f68,negated_conjecture,(
% 2.46/0.68    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 2.46/0.68    inference(negated_conjecture,[],[f67])).
% 2.46/0.68  fof(f67,conjecture,(
% 2.46/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).
% 2.46/0.68  fof(f1437,plain,(
% 2.46/0.68    spl19_4 | ~spl19_3 | ~spl19_6 | spl19_30),
% 2.46/0.68    inference(avatar_split_clause,[],[f1377,f1193,f389,f371,f376])).
% 2.46/0.68  fof(f1377,plain,(
% 2.46/0.68    v3_pre_topc(sK1,sK0) | (~spl19_3 | ~spl19_6 | spl19_30)),
% 2.46/0.68    inference(subsumption_resolution,[],[f1376,f1195])).
% 2.46/0.68  fof(f1195,plain,(
% 2.46/0.68    k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | spl19_30),
% 2.46/0.68    inference(avatar_component_clause,[],[f1193])).
% 2.46/0.68  fof(f1376,plain,(
% 2.46/0.68    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | v3_pre_topc(sK1,sK0) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f989,f1107])).
% 2.46/0.68  fof(f989,plain,(
% 2.46/0.68    k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) | v3_pre_topc(sK1,sK0) | (~spl19_3 | ~spl19_6)),
% 2.46/0.68    inference(forward_demodulation,[],[f210,f762])).
% 2.46/0.68  fof(f210,plain,(
% 2.46/0.68    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | v3_pre_topc(sK1,sK0)),
% 2.46/0.68    inference(cnf_transformation,[],[f154])).
% 2.46/0.68  fof(f1311,plain,(
% 2.46/0.68    spl19_34 | ~spl19_3),
% 2.46/0.68    inference(avatar_split_clause,[],[f551,f371,f1308])).
% 2.46/0.68  fof(f551,plain,(
% 2.46/0.68    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl19_3),
% 2.46/0.68    inference(backward_demodulation,[],[f479,f541])).
% 2.46/0.68  fof(f479,plain,(
% 2.46/0.68    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl19_3),
% 2.46/0.68    inference(unit_resulting_resolution,[],[f373,f303])).
% 2.46/0.68  fof(f303,plain,(
% 2.46/0.68    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.46/0.68    inference(cnf_transformation,[],[f124])).
% 2.46/0.68  fof(f124,plain,(
% 2.46/0.68    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.46/0.68    inference(ennf_transformation,[],[f14])).
% 2.46/0.68  fof(f14,axiom,(
% 2.46/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.46/0.68  fof(f392,plain,(
% 2.46/0.68    spl19_6 | ~spl19_1),
% 2.46/0.68    inference(avatar_split_clause,[],[f384,f361,f389])).
% 2.46/0.68  fof(f384,plain,(
% 2.46/0.68    l1_struct_0(sK0) | ~spl19_1),
% 2.46/0.68    inference(unit_resulting_resolution,[],[f363,f226])).
% 2.46/0.68  fof(f226,plain,(
% 2.46/0.68    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f80])).
% 2.46/0.68  fof(f80,plain,(
% 2.46/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.46/0.68    inference(ennf_transformation,[],[f47])).
% 2.46/0.68  fof(f47,axiom,(
% 2.46/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.46/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.46/0.68  fof(f383,plain,(
% 2.46/0.68    spl19_4 | spl19_5),
% 2.46/0.68    inference(avatar_split_clause,[],[f208,f380,f376])).
% 2.46/0.68  fof(f208,plain,(
% 2.46/0.68    v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 2.46/0.68    inference(cnf_transformation,[],[f154])).
% 2.46/0.68  fof(f374,plain,(
% 2.46/0.68    spl19_3),
% 2.46/0.68    inference(avatar_split_clause,[],[f207,f371])).
% 2.46/0.68  fof(f207,plain,(
% 2.46/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.46/0.68    inference(cnf_transformation,[],[f154])).
% 2.46/0.68  fof(f364,plain,(
% 2.46/0.68    spl19_1),
% 2.46/0.68    inference(avatar_split_clause,[],[f206,f361])).
% 2.46/0.68  fof(f206,plain,(
% 2.46/0.68    l1_pre_topc(sK0)),
% 2.46/0.68    inference(cnf_transformation,[],[f154])).
% 2.46/0.68  % SZS output end Proof for theBenchmark
% 2.46/0.68  % (14265)------------------------------
% 2.46/0.68  % (14265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.46/0.68  % (14265)Termination reason: Refutation
% 2.46/0.68  
% 2.46/0.68  % (14265)Memory used [KB]: 12920
% 2.46/0.68  % (14265)Time elapsed: 0.212 s
% 2.46/0.68  % (14265)------------------------------
% 2.46/0.68  % (14265)------------------------------
% 2.46/0.69  % (14237)Success in time 0.325 s
%------------------------------------------------------------------------------
