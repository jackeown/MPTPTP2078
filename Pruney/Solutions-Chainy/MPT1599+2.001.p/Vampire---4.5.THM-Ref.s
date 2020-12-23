%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 509 expanded)
%              Number of leaves         :   26 ( 144 expanded)
%              Depth                    :   29
%              Number of atoms          :  727 (1926 expanded)
%              Number of equality atoms :   36 ( 300 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (6583)Refutation not found, incomplete strategy% (6583)------------------------------
% (6583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6583)Termination reason: Refutation not found, incomplete strategy

% (6583)Memory used [KB]: 1663
% (6583)Time elapsed: 0.134 s
% (6583)------------------------------
% (6583)------------------------------
fof(f520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f117,f146,f151,f495,f519])).

fof(f519,plain,
    ( ~ spl4_4
    | spl4_5
    | spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f517,f99])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f517,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4
    | spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f516,f150])).

fof(f150,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f516,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl4_4
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f515,f94])).

fof(f94,plain,
    ( v2_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_4
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f515,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f511,f145])).

fof(f145,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_9
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f511,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | spl4_8 ),
    inference(resolution,[],[f116,f277])).

fof(f277,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f275,f135])).

fof(f135,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f134,f68])).

fof(f68,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f134,plain,(
    ! [X0] :
      ( u1_struct_0(k2_yellow_1(X0)) = X0
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f133,plain,(
    ! [X0] :
      ( u1_struct_0(k2_yellow_1(X0)) = X0
      | ~ v1_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k2_yellow_1(X0) != X1
      | u1_struct_0(X1) = X0
      | ~ v1_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(superposition,[],[f123,f72])).

fof(f72,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f123,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(X4,X5) != X3
      | u1_struct_0(X3) = X4
      | ~ v1_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f119,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(X4,X5) != X3
      | u1_struct_0(X3) = X4
      | ~ m1_subset_1(u1_orders_2(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X3))))
      | ~ v1_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(superposition,[],[f62,f65])).

fof(f65,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f274,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f52,f135])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f273,f135])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f272,f70])).

fof(f70,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f271,f71])).

fof(f71,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f268,f68])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f194,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f138,f135])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f50,f135])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f193,f52])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0)
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f192,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0)
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f181,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f74,f66])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(f116,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_8
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f495,plain,
    ( ~ spl4_4
    | spl4_5
    | spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f493,f99])).

fof(f493,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f492,f150])).

fof(f492,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f491,f94])).

fof(f491,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f485,f145])).

fof(f485,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | spl4_7 ),
    inference(resolution,[],[f287,f112])).

fof(f112,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_7
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f286,f153])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f285,f135])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f283,f135])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f282,f70])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f281,f71])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f278,f68])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f200,f152])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f199,f52])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2)
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f198,f66])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2)
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f196,f61])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f195,f52])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f75,f66])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f151,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f137,f82,f148])).

fof(f82,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f137,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f84,f135])).

fof(f84,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f146,plain,
    ( spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f136,f87,f143])).

fof(f87,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f136,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f89,f135])).

fof(f89,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f117,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f108,f77,f114,f110])).

fof(f77,plain,
    ( spl4_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f108,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_1 ),
    inference(resolution,[],[f49,f79])).

fof(f79,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f100,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f44,f97])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f95,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f82])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f48,f77])).

fof(f48,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6587)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (6588)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6604)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (6586)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (6585)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (6584)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (6596)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (6594)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (6602)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (6599)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (6605)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (6599)Refutation not found, incomplete strategy% (6599)------------------------------
% 0.21/0.54  % (6599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6599)Memory used [KB]: 10746
% 0.21/0.54  % (6599)Time elapsed: 0.130 s
% 0.21/0.54  % (6599)------------------------------
% 0.21/0.54  % (6599)------------------------------
% 0.21/0.54  % (6597)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (6611)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (6607)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (6582)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (6606)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (6583)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (6612)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (6604)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (6601)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (6589)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (6598)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (6609)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (6610)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (6603)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  % (6583)Refutation not found, incomplete strategy% (6583)------------------------------
% 0.21/0.55  % (6583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6583)Memory used [KB]: 1663
% 0.21/0.55  % (6583)Time elapsed: 0.134 s
% 0.21/0.55  % (6583)------------------------------
% 0.21/0.55  % (6583)------------------------------
% 0.21/0.55  fof(f520,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f117,f146,f151,f495,f519])).
% 0.21/0.55  fof(f519,plain,(
% 0.21/0.55    ~spl4_4 | spl4_5 | spl4_8 | ~spl4_9 | ~spl4_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f518])).
% 0.21/0.55  fof(f518,plain,(
% 0.21/0.55    $false | (~spl4_4 | spl4_5 | spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f517,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~v1_xboole_0(sK0) | spl4_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl4_5 <=> v1_xboole_0(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f517,plain,(
% 0.21/0.55    v1_xboole_0(sK0) | (~spl4_4 | spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f516,f150])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    m1_subset_1(sK2,sK0) | ~spl4_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    spl4_10 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.55  fof(f516,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | (~spl4_4 | spl4_8 | ~spl4_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f515,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    v2_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    spl4_4 <=> v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.55  fof(f515,plain,(
% 0.21/0.55    ~v2_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | (spl4_8 | ~spl4_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f511,f145])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    m1_subset_1(sK1,sK0) | ~spl4_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f143])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    spl4_9 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,sK0) | ~v2_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | spl4_8),
% 0.21/0.55    inference(resolution,[],[f116,f277])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | ~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f276])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f275,f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f134,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0 | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0 | ~v1_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(equality_resolution,[],[f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_yellow_1(X0) != X1 | u1_struct_0(X1) = X0 | ~v1_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.21/0.55    inference(superposition,[],[f123,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X4,X5,X3] : (g1_orders_2(X4,X5) != X3 | u1_struct_0(X3) = X4 | ~v1_orders_2(X3) | ~l1_orders_2(X3)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f119,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ( ! [X4,X5,X3] : (g1_orders_2(X4,X5) != X3 | u1_struct_0(X3) = X4 | ~m1_subset_1(u1_orders_2(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X3)))) | ~v1_orders_2(X3) | ~l1_orders_2(X3)) )),
% 0.21/0.55    inference(superposition,[],[f62,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f274,f153])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f139,f68])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(superposition,[],[f52,f135])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f273,f135])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f272,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f271,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f268,f68])).
% 0.21/0.55  fof(f268,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v2_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X2,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X2) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(resolution,[],[f194,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f138,f135])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f50,f135])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v3_orders_2(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f193,f52])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~v3_orders_2(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f192,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(resolution,[],[f181,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f180,f52])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f74,f66])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(rectify,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl4_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    spl4_8 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.55  fof(f495,plain,(
% 0.21/0.55    ~spl4_4 | spl4_5 | spl4_7 | ~spl4_9 | ~spl4_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f494])).
% 0.21/0.55  fof(f494,plain,(
% 0.21/0.55    $false | (~spl4_4 | spl4_5 | spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f493,f99])).
% 0.21/0.55  fof(f493,plain,(
% 0.21/0.55    v1_xboole_0(sK0) | (~spl4_4 | spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f492,f150])).
% 0.21/0.55  fof(f492,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | (~spl4_4 | spl4_7 | ~spl4_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f491,f94])).
% 0.21/0.55  fof(f491,plain,(
% 0.21/0.55    ~v2_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | (spl4_7 | ~spl4_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f485,f145])).
% 0.21/0.55  fof(f485,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,sK0) | ~v2_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | spl4_7),
% 0.21/0.55    inference(resolution,[],[f287,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl4_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f110])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    spl4_7 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | ~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f286,f153])).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f285,f135])).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f284])).
% 0.21/0.55  fof(f284,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f283,f135])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f282,f70])).
% 0.21/0.55  fof(f282,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f281,f71])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f278,f68])).
% 0.21/0.55  fof(f278,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v2_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | r1_tarski(k11_lattice3(k2_yellow_1(X1),X0,X2),X0) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(resolution,[],[f200,f152])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v3_orders_2(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f199,f52])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~v3_orders_2(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f198,f66])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | r3_orders_2(X1,k11_lattice3(X1,X2,X0),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(resolution,[],[f196,f61])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f195,f52])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f75,f66])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    spl4_10 | ~spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f137,f82,f148])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    m1_subset_1(sK2,sK0) | ~spl4_2),
% 0.21/0.55    inference(backward_demodulation,[],[f84,f135])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    spl4_9 | ~spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f136,f87,f143])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.21/0.55    inference(backward_demodulation,[],[f89,f135])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f87])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~spl4_7 | ~spl4_8 | spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f108,f77,f114,f110])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    spl4_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl4_1),
% 0.21/0.55    inference(resolution,[],[f49,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) | spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f77])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~spl4_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f44,f97])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ~v1_xboole_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f35,f34,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f13])).
% 0.21/0.55  fof(f13,conjecture,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f45,f92])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f46,f87])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f47,f82])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ~spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f48,f77])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6604)------------------------------
% 0.21/0.55  % (6604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6604)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6604)Memory used [KB]: 6524
% 0.21/0.55  % (6604)Time elapsed: 0.134 s
% 0.21/0.55  % (6604)------------------------------
% 0.21/0.55  % (6604)------------------------------
% 0.21/0.55  % (6600)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (6593)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (6579)Success in time 0.187 s
%------------------------------------------------------------------------------
