%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1225+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 218 expanded)
%              Number of leaves         :   20 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 ( 834 expanded)
%              Number of equality atoms :   45 ( 150 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3837,f3842,f3847,f3857,f3867,f3887,f3928,f3954,f4701,f5287])).

fof(f5287,plain,
    ( ~ spl147_1
    | ~ spl147_7
    | spl147_17
    | ~ spl147_28 ),
    inference(avatar_contradiction_clause,[],[f5286])).

fof(f5286,plain,
    ( $false
    | ~ spl147_1
    | ~ spl147_7
    | spl147_17
    | ~ spl147_28 ),
    inference(subsumption_resolution,[],[f5276,f4061])).

fof(f4061,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK4),k2_pre_topc(sK2,k3_xboole_0(X0,sK4)))
    | ~ spl147_1
    | ~ spl147_7 ),
    inference(unit_resulting_resolution,[],[f3836,f3922,f2852])).

fof(f2852,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1839])).

fof(f1839,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f3922,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl147_7 ),
    inference(backward_demodulation,[],[f3911,f3918])).

fof(f3918,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK4) = k3_xboole_0(X0,sK4)
    | ~ spl147_7 ),
    inference(unit_resulting_resolution,[],[f3866,f2859])).

fof(f2859,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2128,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f3866,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl147_7 ),
    inference(avatar_component_clause,[],[f3864])).

fof(f3864,plain,
    ( spl147_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_7])])).

fof(f3911,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl147_7 ),
    inference(unit_resulting_resolution,[],[f3866,f2860])).

fof(f2860,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2129])).

fof(f2129,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f3836,plain,
    ( l1_pre_topc(sK2)
    | ~ spl147_1 ),
    inference(avatar_component_clause,[],[f3834])).

fof(f3834,plain,
    ( spl147_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_1])])).

fof(f5276,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK4),k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)))
    | spl147_17
    | ~ spl147_28 ),
    inference(unit_resulting_resolution,[],[f3953,f4700,f2900])).

fof(f2900,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2587])).

fof(f2587,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2586])).

fof(f2586,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4700,plain,
    ( r1_tarski(k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
    | ~ spl147_28 ),
    inference(avatar_component_clause,[],[f4698])).

fof(f4698,plain,
    ( spl147_28
  <=> r1_tarski(k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_28])])).

fof(f3953,plain,
    ( k3_xboole_0(sK3,sK4) != k2_pre_topc(sK2,k3_xboole_0(sK3,sK4))
    | spl147_17 ),
    inference(avatar_component_clause,[],[f3951])).

fof(f3951,plain,
    ( spl147_17
  <=> k3_xboole_0(sK3,sK4) = k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_17])])).

fof(f4701,plain,
    ( spl147_28
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(avatar_split_clause,[],[f4028,f3864,f3854,f3844,f3839,f3834,f4698])).

fof(f3839,plain,
    ( spl147_2
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_2])])).

fof(f3844,plain,
    ( spl147_3
  <=> v4_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_3])])).

fof(f3854,plain,
    ( spl147_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_5])])).

fof(f4028,plain,
    ( r1_tarski(k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f4027,f3918])).

fof(f4027,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k3_xboole_0(sK3,sK4))
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f4026,f2985])).

fof(f2985,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4026,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k3_xboole_0(sK4,sK3))
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f4025,f3939])).

fof(f3939,plain,
    ( sK3 = k2_pre_topc(sK2,sK3)
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_5 ),
    inference(unit_resulting_resolution,[],[f3836,f3841,f3856,f2850])).

fof(f2850,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2120])).

fof(f2120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2119])).

fof(f2119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f3856,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl147_5 ),
    inference(avatar_component_clause,[],[f3854])).

fof(f3841,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ spl147_2 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f4025,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k3_xboole_0(sK4,k2_pre_topc(sK2,sK3)))
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f4024,f2985])).

fof(f4024,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k3_xboole_0(k2_pre_topc(sK2,sK3),sK4))
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f4023,f3918])).

fof(f4023,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK4))
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(forward_demodulation,[],[f3996,f3940])).

fof(f3940,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_7 ),
    inference(unit_resulting_resolution,[],[f3836,f3846,f3866,f2850])).

fof(f3846,plain,
    ( v4_pre_topc(sK4,sK2)
    | ~ spl147_3 ),
    inference(avatar_component_clause,[],[f3844])).

fof(f3996,plain,
    ( r1_tarski(k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)),k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))
    | ~ spl147_1
    | ~ spl147_5
    | ~ spl147_7 ),
    inference(unit_resulting_resolution,[],[f3836,f3856,f3866,f2844])).

fof(f2844,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1842])).

fof(f1842,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f3954,plain,
    ( ~ spl147_17
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7
    | spl147_16 ),
    inference(avatar_split_clause,[],[f3949,f3925,f3864,f3854,f3844,f3839,f3834,f3951])).

fof(f3925,plain,
    ( spl147_16
  <=> k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_16])])).

fof(f3949,plain,
    ( k3_xboole_0(sK3,sK4) != k2_pre_topc(sK2,k3_xboole_0(sK3,sK4))
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7
    | spl147_16 ),
    inference(forward_demodulation,[],[f3946,f2985])).

fof(f3946,plain,
    ( k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(sK4,sK3)
    | ~ spl147_1
    | ~ spl147_2
    | ~ spl147_3
    | ~ spl147_5
    | ~ spl147_7
    | spl147_16 ),
    inference(backward_demodulation,[],[f3945,f3939])).

fof(f3945,plain,
    ( k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(sK4,k2_pre_topc(sK2,sK3))
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_7
    | spl147_16 ),
    inference(forward_demodulation,[],[f3944,f2985])).

fof(f3944,plain,
    ( k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_pre_topc(sK2,sK3),sK4)
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_7
    | spl147_16 ),
    inference(forward_demodulation,[],[f3942,f3918])).

fof(f3942,plain,
    ( k2_pre_topc(sK2,k3_xboole_0(sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK4)
    | ~ spl147_1
    | ~ spl147_3
    | ~ spl147_7
    | spl147_16 ),
    inference(backward_demodulation,[],[f3927,f3940])).

fof(f3927,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) != k2_pre_topc(sK2,k3_xboole_0(sK3,sK4))
    | spl147_16 ),
    inference(avatar_component_clause,[],[f3925])).

fof(f3928,plain,
    ( ~ spl147_16
    | ~ spl147_7
    | spl147_11 ),
    inference(avatar_split_clause,[],[f3921,f3884,f3864,f3925])).

fof(f3884,plain,
    ( spl147_11
  <=> k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl147_11])])).

fof(f3921,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) != k2_pre_topc(sK2,k3_xboole_0(sK3,sK4))
    | ~ spl147_7
    | spl147_11 ),
    inference(backward_demodulation,[],[f3886,f3918])).

fof(f3886,plain,
    ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    | spl147_11 ),
    inference(avatar_component_clause,[],[f3884])).

fof(f3887,plain,(
    ~ spl147_11 ),
    inference(avatar_split_clause,[],[f2838,f3884])).

fof(f2838,plain,(
    k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(cnf_transformation,[],[f2551])).

fof(f2551,plain,
    ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    & v4_pre_topc(sK4,sK2)
    & v4_pre_topc(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f2105,f2550,f2549,f2548])).

fof(f2548,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),X1,X2)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X2))
              & v4_pre_topc(X2,sK2)
              & v4_pre_topc(X1,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2549,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),X1,X2)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X2))
            & v4_pre_topc(X2,sK2)
            & v4_pre_topc(X1,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,X2)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X2))
          & v4_pre_topc(X2,sK2)
          & v4_pre_topc(sK3,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2550,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,X2)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X2))
        & v4_pre_topc(X2,sK2)
        & v4_pre_topc(sK3,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k2_pre_topc(sK2,k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
      & v4_pre_topc(sK4,sK2)
      & v4_pre_topc(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2105,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2104])).

fof(f2104,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2094])).

fof(f2094,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2093])).

fof(f2093,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

fof(f3867,plain,(
    spl147_7 ),
    inference(avatar_split_clause,[],[f2835,f3864])).

fof(f2835,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2551])).

fof(f3857,plain,(
    spl147_5 ),
    inference(avatar_split_clause,[],[f2834,f3854])).

fof(f2834,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2551])).

fof(f3847,plain,(
    spl147_3 ),
    inference(avatar_split_clause,[],[f2837,f3844])).

fof(f2837,plain,(
    v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f2551])).

fof(f3842,plain,(
    spl147_2 ),
    inference(avatar_split_clause,[],[f2836,f3839])).

fof(f2836,plain,(
    v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f2551])).

fof(f3837,plain,(
    spl147_1 ),
    inference(avatar_split_clause,[],[f2833,f3834])).

fof(f2833,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2551])).
%------------------------------------------------------------------------------
